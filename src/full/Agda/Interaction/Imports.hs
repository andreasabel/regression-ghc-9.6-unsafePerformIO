{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE RecursiveDo #-}

{-# OPTIONS_GHC -Wall #-}

{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports
  ( Source(..)
  , parseSource
  , typeCheckMain
  ) where

import Prelude hiding (null)

import qualified Data.Map as Map
import qualified Data.Text.Lazy as TL

import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Attribute
import Agda.Syntax.Common
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Translation.ConcreteToAbstract as CToA

import Agda.TypeChecking.Warnings hiding (warnings)
import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.Interaction.FindFile
import Agda.Interaction.Library.Base (OptionsPragma(..))
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens

import Agda.Utils.FileName
import Agda.Utils.Pretty hiding (Mode)

type AgdaLibFile = ()

-- | The decorated source code.

data Source = Source
  { srcText        :: TL.Text               -- ^ Source code.
  , srcFileType    :: FileType              -- ^ Source file type
  , srcOrigin      :: SourceFile            -- ^ Source location at the time of its parsing
  , srcModule      :: C.Module              -- ^ The parsed module.
  , srcModuleName  :: TopLevelModuleName    -- ^ The top-level module name.
  , srcProjectLibs :: [AgdaLibFile]         -- ^ The .agda-lib file(s) of the project this file belongs to.
  , srcAttributes  :: !Attributes
    -- ^ Every encountered attribute.
  }

-- | Parses a source file and prepares the 'Source' record.

parseSource :: SourceFile -> TCM Source
parseSource sourceFile@(SourceFile f) = Bench.billTo [Bench.Parsing] $ do
  (source, fileType, parsedMod, attrs, parsedModName) <- mdo
    -- This piece of code uses mdo because the top-level module name
    -- (parsedModName) is obtained from the parser's result, but it is
    -- also used by the parser.
    let rf = mkRangeFile f (Just parsedModName)
    source                         <- runPM $ readFilePM rf
    ((parsedMod, attrs), fileType) <- runPM $
                                      parseFile moduleParser rf $
                                      TL.unpack source
    parsedModName                  <- moduleName f parsedMod
    return (source, fileType, parsedMod, attrs, parsedModName)
  return Source
    { srcText        = source
    , srcFileType    = fileType
    , srcOrigin      = sourceFile
    , srcModule      = parsedMod
    , srcModuleName  = parsedModName
    , srcProjectLibs = []
    , srcAttributes  = attrs
    }

srcFilePragmas :: Source -> [OptionsPragma]
srcFilePragmas src = pragmas
  where
  cpragmas = C.modPragmas (srcModule src)
  pragmas = [ OptionsPragma
                { pragmaStrings = opts
                , pragmaRange   = r
                }
            | C.OptionsPragma r opts <- cpragmas
            ]

-- | Set options from a 'Source' pragma, using the source
--   ranges of the pragmas for error reporting.
setOptionsFromSourcePragmas :: Source -> TCM ()
setOptionsFromSourcePragmas src = do
  mapM_ setOptionsFromPragma (srcFilePragmas    src)

-- | Is the aim to type-check the top-level module, or only to
-- scope-check it?

data Mode
  = ScopeCheck
  | TypeCheck
  deriving (Eq, Show)


-- | The result and associated parameters of a type-checked file,
--   when invoked directly via interaction or a backend.
--   Note that the constructor is not exported.

type CheckResult = ()

-- | Type checks the main file of the interaction.
--   This could be the file loaded in the interacting editor (emacs),
--   or the file passed on the command line.
--
--   First, the primitive modules are imported.
--   Then, @getInterface@ is called to do the main work.
--
--   If the 'Mode' is 'ScopeCheck', then type-checking is not
--   performed, only scope-checking. (This may include type-checking
--   of imported modules.) In this case the generated, partial
--   interface is not stored in the state ('stDecodedModules'). Note,
--   however, that if the file has already been type-checked, then a
--   complete interface is returned.

typeCheckMain
  :: Source
     -- ^ The decorated source code.
  -> TCM CheckResult
typeCheckMain src = do
  -- liftIO $ putStrLn $ "This is typeCheckMain " ++ prettyShow f
  -- liftIO . putStrLn . show =<< getVerbosity

  -- For the main interface, we also remember the pragmas from the file
  setOptionsFromSourcePragmas src

  -- Now do the type checking via getInterface.
  checkModuleName' (srcModuleName src) (srcOrigin src)

  mi <- getInterface (srcModuleName src) src

  stCurrentModule `setTCLens'`
    Just ( iModuleName (miInterface mi)
         , iTopLevelModuleName (miInterface mi)
         )

  return ()
  where
  checkModuleName' m f =
    -- Andreas, 2016-07-11, issue 2092
    -- The error range should be set to the file with the wrong module name
    -- not the importing one (which would be the default).
    setCurrentRange m $ checkModuleName m f Nothing


getInterface
  :: TopLevelModuleName
  -> Source
  -> TCM ModuleInfo
getInterface x src = do
     -- We remember but reset the pragma options locally
     -- Issue #3644 (Abel 2020-05-08): Set approximate range for errors in options
     setCurrentRange (C.modPragmas . srcModule <$> Just src) $
       -- Now reset the options
       setCommandLineOptions . stPersistentOptions . stPersistentState =<< getTC

     let file = srcOrigin src
     modifyTCLens stModuleToSource $ Map.insert x (srcFilePath file)

     setCommandLineOptions . stPersistentOptions . stPersistentState =<< getTC
     createInterface x file src


-- | Tries to type check a module and write out its interface. The
-- function only writes out an interface file if it does not encounter
-- any warnings.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: TopLevelModuleName    -- ^ The expected module name.
  -> SourceFile            -- ^ The file to type check.
  -> Source
  -> TCM ModuleInfo
createInterface mname file src = do
  Bench.billTo [Bench.TopModule mname] $ do
    localTC (\e -> e { envCurrentPath = Just (srcFilePath file) }) $ do

    reportSLn "import.iface.create" 5 $
      "Creating interface for " ++ prettyShow mname ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- prettyShow <$> getPrettyVisitedModules
      reportSLn "import.iface.create" 10 $ "  visited: " ++ visited

    let srcPath = srcFilePath $ srcOrigin src

    setOptionsFromSourcePragmas src
    checkAttributes (srcAttributes src)
    syntactic <- optSyntacticEquality <$> pragmaOptions
    localTC (\env -> env { envSyntacticEqualityFuel = syntactic }) $ do

    verboseS "import.iface.create" 15 $ do
      nestingLevel      <- asksTC (pred . length . envImportPath)
      highlightingLevel <- asksTC envHighlightingLevel
      reportSLn "import.iface.create" 15 $ unlines
        [ "  nesting      level: " ++ show nestingLevel
        , "  highlighting level: " ++ show highlightingLevel
        ]

    -- Scope checking.
    reportSLn "import.iface.create" 7 "Starting scope checking."
    _topLevel <- Bench.billTo [Bench.Scoping] $ do
      let topDecls = C.modDecls $ srcModule src
      concreteToAbstract_ (TopLevel srcPath mname topDecls)
    reportSLn "import.iface.create" 7 "Finished scope checking."

    isPrimitiveModule <- Lens.isPrimitiveModule (filePath srcPath)

    return ModuleInfo
      { miInterface = undefined
      , miWarnings = undefined
      , miPrimitive = isPrimitiveModule
      , miMode = ModuleTypeChecked
      }
