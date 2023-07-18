{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE RecursiveDo #-}

{-# OPTIONS_GHC -Wall #-}

{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports
  ( pattern TypeCheck
  , Source(..)
  , scopeCheckImport
  , parseSource
  , typeCheckMain
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Maybe

import qualified Data.List as List

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.Lazy as TL

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Attribute
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Translation.ConcreteToAbstract as CToA

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Warnings hiding (warnings)
import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.Interaction.FindFile
import Agda.Interaction.Library.Base (OptionsPragma(..))
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens

import Agda.Utils.FileName
import Agda.Utils.Maybe
import Agda.Utils.Monad
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

srcDefaultPragmas :: Source -> [OptionsPragma]
srcDefaultPragmas _ = []

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
  mapM_ setOptionsFromPragma (srcDefaultPragmas src)
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

-- | The kind of interface produced by 'createInterface'
moduleCheckMode :: MainInterface -> ModuleCheckMode
moduleCheckMode = \case
    MainInterface TypeCheck                       -> ModuleTypeChecked
    NotMainInterface                              -> ModuleTypeChecked
    MainInterface ScopeCheck                      -> ModuleScopeChecked

-- | Merge an interface into the current proof state.
mergeInterface :: Interface -> TCM ()
mergeInterface i = do
    let sig     = iSignature i
        warns   = iWarnings i
    addImportedThings
      sig
      (iMetaBindings i)
      (iPatternSyns i)
      (iDisplayForms i)
      (iUserWarnings i)
      (iPartialDefs i)
      warns
      (iOpaqueBlocks i)
      (iOpaqueNames i)

addImportedThings
  :: Signature
  -> RemoteMetaStore
  -> A.PatternSynDefns
  -> DisplayForms
  -> Map A.QName Text      -- ^ Imported user warnings
  -> Set QName             -- ^ Name of imported definitions which are partial
  -> [TCWarning]
  -> Map OpaqueId OpaqueBlock
  -> Map QName OpaqueId
  -> TCM ()
addImportedThings isig metas patsyns display userwarn
                  partialdefs warnings oblock oid = do
  stImports              `modifyTCLens` \ imp -> unionSignatures [imp, isig]
  stImportedMetaStore    `modifyTCLens` HMap.union metas
  stImportedUserWarnings `modifyTCLens` \ imp -> Map.union imp userwarn
  stImportedPartialDefs  `modifyTCLens` \ imp -> Set.union imp partialdefs
  stPatternSynImports    `modifyTCLens` \ imp -> Map.union imp patsyns
  stImportedDisplayForms `modifyTCLens` \ imp -> HMap.unionWith (++) imp display
  stTCWarnings           `modifyTCLens` \ imp -> imp `List.union` warnings
  stOpaqueBlocks         `modifyTCLens` \ imp -> imp `Map.union` oblock
  stOpaqueIds            `modifyTCLens` \ imp -> imp `Map.union` oid
  addImportedInstances isig

-- | Scope checks the given module. A proper version of the module
-- name (with correct definition sites) is returned.

scopeCheckImport ::
  TopLevelModuleName -> ModuleName ->
  TCM (ModuleName, Map ModuleName Scope)
scopeCheckImport top x = do
    reportSLn "import.scope" 5 $ "Scope checking " ++ prettyShow x
    verboseS "import.scope" 10 $ do
      visited <- prettyShow <$> getPrettyVisitedModules
      reportSLn "import.scope" 10 $ "  visited: " ++ visited
    -- Since scopeCheckImport is called from the scope checker,
    -- we need to reimburse her account.
    i <- Bench.billTo [] $ getNonMainInterface top Nothing
    addImport top

    -- If that interface was supposed to raise a warning on import, do so.
    whenJust (iImportWarning i) $ warning . UserWarning

    -- let s = publicModules $ iInsideScope i
    let s = iScope i
    return (iModuleName i `withRangesOfQ` mnameToConcrete x, s)

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

-- | Tries to return the interface associated to the given (imported) module.
--   The time stamp of the relevant interface file is also returned.
--   Calls itself recursively for the imports of the given module.
--   May type check the module.
--   An error is raised if a warning is encountered.
--
--   Do not use this for the main file, use 'typeCheckMain' instead.

getNonMainInterface
  :: TopLevelModuleName
  -> Maybe Source
     -- ^ Optional: the source code and some information about the source code.
  -> TCM Interface
getNonMainInterface x msrc = do
  -- Preserve/restore the current pragma options, which will be mutated when loading
  -- and checking the interface.
  mi <- bracket_ (useTC stPragmaOptions) (stPragmaOptions `setTCLens`) $
          getInterface x NotMainInterface msrc
  tcWarningsToError $ miWarnings mi
  return (miInterface mi)

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
      case isMain of
        MainInterface _ -> createInterface x file isMain msrc
        NotMainInterface -> createInterfaceIsolated x file msrc



loadDecodedModule
  :: SourceFile
     -- ^ File we process.
  -> ModuleInfo
  -> ExceptT String TCM ModuleInfo
loadDecodedModule file mi = do
  let fp = filePath $ srcFilePath file
  let i = miInterface mi

  -- Check that it's the right version
  reportSLn "import.iface" 5 $ "  imports: " ++ prettyShow (iImportedModules i)

  -- We set the pragma options of the skipped file here, so that
  -- we can check that they are compatible with those of the
  -- imported modules. Also, if the top-level file is skipped we
  -- want the pragmas to apply to interactive commands in the UI.
  -- Jesper, 2021-04-18: Check for changed options in library files!
  -- (see #5250)
  libOptions <- lift $ getLibraryOptions
    (srcFilePath file)
    (iTopLevelModuleName i)
  lift $ mapM_ setOptionsFromPragma (libOptions ++ iFilePragmaOptions i)

  -- Check that options that matter haven't changed compared to
  -- current options (issue #2487)
  unlessM (lift $ Lens.isBuiltinModule fp) $ do
    current <- useTC stPragmaOptions
    when (recheckBecausePragmaOptionsChanged (iOptionsUsed i) current) $
      throwError "options changed"

  reportSLn "import.iface" 5 "  New module. Let's check it out."
  lift $ mergeInterface i

  return mi

-- | Run the type checker on a file and create an interface.
--
--   Mostly, this function calls 'createInterface'.
--   But if it is not the main module we check,
--   we do it in a fresh state, suitably initialize,
--   in order to forget some state changes after successful type checking.

createInterfaceIsolated
  :: TopLevelModuleName
     -- ^ Module name of file we process.
  -> SourceFile
     -- ^ File we process.
  -> Maybe Source
     -- ^ Optional: the source code and some information about the source code.
  -> TCM ModuleInfo
createInterfaceIsolated x file msrc = do

      ms          <- getImportPath
      range       <- asksTC envRange
      call        <- asksTC envCall
      mf          <- useTC stModuleToSource
      vs          <- getVisitedModules
      ds          <- getDecodedModules
      opts        <- stPersistentOptions . stPersistentState <$> getTC
      isig        <- useTC stImports
      metas       <- useTC stImportedMetaStore
      display     <- useTC stImportsDisplayForms
      userwarn    <- useTC stImportedUserWarnings
      partialdefs <- useTC stImportedPartialDefs
      opaqueblk   <- useTC stOpaqueBlocks
      opaqueid    <- useTC stOpaqueIds
      ipatsyns <- getPatternSynImports
      -- Every interface is treated in isolation. Note: Some changes to
      -- the persistent state may not be preserved if an error other
      -- than a type error or an IO exception is encountered in an
      -- imported module.
      (mi, newModToSource, newDecodedModules) <- (either throwError pure =<<) $
           -- The cache should not be used for an imported module, and it
           -- should be restored after the module has been type-checked
           freshTCM $
             withImportPath ms $
             localTC (\e -> e
                              -- Andreas, 2014-08-18:
                              -- Preserve the range of import statement
                              -- for reporting termination errors in
                              -- imported modules:
                            { envRange              = range
                            , envCall               = call
                            }) $ do
               setDecodedModules ds
               setCommandLineOptions opts
               stModuleToSource `setTCLens` mf
               setVisitedModules vs
               addImportedThings isig metas ipatsyns display
                 userwarn partialdefs [] opaqueblk opaqueid

               r  <- createInterface x file NotMainInterface msrc
               mf' <- useTC stModuleToSource
               ds' <- getDecodedModules
               return (r, mf', ds')

      stModuleToSource `setTCLens` newModToSource
      setDecodedModules newDecodedModules

      -- We skip the file which has just been type-checked to
      -- be able to forget some of the local state from
      -- checking the module.
      -- Note that this doesn't actually read the interface
      -- file, only the cached interface. (This comment is not
      -- correct, see
      -- test/Fail/customised/NestedProjectRoots.err.)
      validated <- runExceptT $ loadDecodedModule file mi

      -- NOTE: This attempts to type-check FOREVER if for some
      -- reason it continually fails to validate interface.
      let recheckOnError = \msg -> do
            reportSLn "import.iface" 1 $ "Failed to validate just-loaded interface: " ++ msg
            createInterfaceIsolated x file msrc

      either recheckOnError pure validated


-- | Tries to type check a module and write out its interface. The
-- function only writes out an interface file if it does not encounter
-- any warnings.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: TopLevelModuleName    -- ^ The expected module name.
  -> SourceFile            -- ^ The file to type check.
  -> MainInterface         -- ^ Are we dealing with the main module?
  -> Maybe Source      -- ^ Optional information about the source code.
  -> TCM ModuleInfo
createInterface mname file isMain msrc = do
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
      , miMode = moduleCheckMode isMain
      }
