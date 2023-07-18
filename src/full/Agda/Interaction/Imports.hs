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

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Maybe

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
import Agda.Utils.Maybe
import Agda.Utils.Null
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

-- | Are we loading the interface for the user-loaded file
--   or for an import?
data MainInterface
  = MainInterface Mode -- ^ For the main file.
                       --
                       --   In this case state changes inflicted by
                       --   'createInterface' are preserved.
  | NotMainInterface   -- ^ For an imported file.
                       --
                       --   In this case state changes inflicted by
                       --   'createInterface' are not preserved.
  deriving (Eq, Show)

-- | If the module has already been visited (without warnings), then
-- its interface is returned directly. Otherwise the computation is
-- used to find the interface and the computed interface is stored for
-- potential later use.

alreadyVisited :: TopLevelModuleName ->
                  MainInterface ->
                  PragmaOptions ->
                  TCM ModuleInfo ->
                  TCM ModuleInfo
alreadyVisited x isMain _currentOptions getModule =
  case isMain of
    MainInterface TypeCheck                       -> useExistingOrLoadAndRecordVisited ModuleTypeChecked
    NotMainInterface                              -> useExistingOrLoadAndRecordVisited ModuleTypeChecked
    MainInterface ScopeCheck                      -> useExistingOrLoadAndRecordVisited ModuleScopeChecked
  where
  useExistingOrLoadAndRecordVisited :: ModuleCheckMode -> TCM ModuleInfo
  useExistingOrLoadAndRecordVisited mode = fromMaybeM loadAndRecordVisited (existingWithoutWarnings mode)

  -- Case: already visited.
  --
  -- A module with warnings should never be allowed to be
  -- imported from another module.
  existingWithoutWarnings :: ModuleCheckMode -> TCM (Maybe ModuleInfo)
  existingWithoutWarnings mode = runMaybeT $ exceptToMaybeT $ do
    mi <- maybeToExceptT "interface has not been visited in this context" $ MaybeT $
      getVisitedModule x

    when (miMode mi < mode) $
      throwError "previously-visited interface was not sufficiently checked"

    unless (null $ miWarnings mi) $
      throwError "previously-visited interface had warnings"

    reportSLn "import.visit" 10 $ "  Already visited " ++ prettyShow x

    lift $ return mi

  loadAndRecordVisited :: TCM ModuleInfo
  loadAndRecordVisited = do
    reportSLn "import.visit" 5 $ "  Getting interface for " ++ prettyShow x
    mi <- getModule
    reportSLn "import.visit" 5 $ "  Now we've looked at " ++ prettyShow x

    -- Interfaces are not stored if we are only scope-checking, or
    -- if any warnings were encountered.
    case (isMain, miWarnings mi) of
      (MainInterface ScopeCheck, _) -> return ()
      (_, _:_)                      -> return ()
      _                             -> storeDecodedModule mi

    reportS "warning.import" 10
      [ "module: " ++ show (moduleNameParts x)
      , "WarningOnImport: " ++ show (iImportWarning (miInterface mi))
      ]

    visitModule mi
    return mi


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

  mi <- getInterface (srcModuleName src) (MainInterface TypeCheck) (Just src)

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


-- | A more precise variant of 'getNonMainInterface'. If warnings are
-- encountered then they are returned instead of being turned into
-- errors.

getInterface
  :: TopLevelModuleName
  -> MainInterface
  -> Maybe Source
     -- ^ Optional: the source code and some information about the source code.
  -> TCM ModuleInfo
getInterface x isMain msrc =
  addImportCycleCheck x $ do
     -- We remember but reset the pragma options locally
     -- Issue #3644 (Abel 2020-05-08): Set approximate range for errors in options
     currentOptions <- useTC stPragmaOptions
     setCurrentRange (C.modPragmas . srcModule <$> msrc) $
       -- Now reset the options
       setCommandLineOptions . stPersistentOptions . stPersistentState =<< getTC

     alreadyVisited x isMain currentOptions $ do
      file <- case msrc of
        Nothing  -> findFile x
        Just src -> do
          -- Andreas, 2021-08-17, issue #5508.
          -- So it happened with @msrc == Just{}@ that the file was not added to @ModuleToSource@,
          -- only with @msrc == Nothing@ (then @findFile@ does it).
          -- As a consequence, the file was added later, but with a file name constructed
          -- from a module name.  As #5508 shows, this can be fatal in case-insensitive file systems.
          -- The file name (with case variant) then no longer maps to the module name.
          -- To prevent this, we register the connection in @ModuleToSource@ here,
          -- where we have the correct spelling of the file name.
          let file = srcOrigin src
          modifyTCLens stModuleToSource $ Map.insert x (srcFilePath file)
          pure file

      setCommandLineOptions . stPersistentOptions . stPersistentState =<< getTC
      createInterface x file msrc


-- | Tries to type check a module and write out its interface. The
-- function only writes out an interface file if it does not encounter
-- any warnings.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: TopLevelModuleName    -- ^ The expected module name.
  -> SourceFile            -- ^ The file to type check.
  -> Maybe Source      -- ^ Optional information about the source code.
  -> TCM ModuleInfo
createInterface mname file msrc = do
  Bench.billTo [Bench.TopModule mname] $ do
    localTC (\e -> e { envCurrentPath = Just (srcFilePath file) }) $ do

    reportSLn "import.iface.create" 5 $
      "Creating interface for " ++ prettyShow mname ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- prettyShow <$> getPrettyVisitedModules
      reportSLn "import.iface.create" 10 $ "  visited: " ++ visited

    src <- maybe (parseSource file) pure msrc

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
