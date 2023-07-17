{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE RecursiveDo #-}

{-# OPTIONS_GHC -Wall #-}

{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports
  ( Mode, pattern ScopeCheck, pattern TypeCheck

  , CheckResult (CheckResult)
  , crModuleInfo
  , crInterface
  , crWarnings
  , crMode
  , crSource

  , Source(..)
  , scopeCheckImport
  , parseSource
  , typeCheckMain
  ) where

import Prelude hiding (null)

import Control.Monad               ( forM, forM_, void )
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Maybe

import Data.Either
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.Lazy as TL

import System.FilePath ((</>))

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
import Agda.TypeChecking.Pretty as P
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.Interaction.FindFile
import Agda.Interaction.Library
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Options.Warnings (unsolvedWarnings)

import Agda.Utils.FileName
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty hiding (Mode)
import Agda.Utils.Hash
import qualified Agda.Utils.Trie as Trie

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
  libs <- getAgdaLibFiles f parsedModName
  return Source
    { srcText        = source
    , srcFileType    = fileType
    , srcOrigin      = sourceFile
    , srcModule      = parsedMod
    , srcModuleName  = parsedModName
    , srcProjectLibs = libs
    , srcAttributes  = attrs
    }

srcDefaultPragmas :: Source -> [OptionsPragma]
srcDefaultPragmas src = map _libPragmas (srcProjectLibs src)

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
alreadyVisited x isMain currentOptions getModule =
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

    lift $ processResultingModule mi

  processResultingModule :: ModuleInfo -> TCM ModuleInfo
  processResultingModule mi = do
    let ModuleInfo { miInterface = i, miPrimitive = isPrim, miWarnings = ws } = mi

    -- Check that imported options are compatible with current ones (issue #2487),
    -- but give primitive modules a pass
    -- compute updated warnings if needed
    wt <- fromMaybe ws <$> (getOptionsCompatibilityWarnings isMain isPrim currentOptions i)

    return mi { miWarnings = wt }

  loadAndRecordVisited :: TCM ModuleInfo
  loadAndRecordVisited = do
    reportSLn "import.visit" 5 $ "  Getting interface for " ++ prettyShow x
    mi <- processResultingModule =<< getModule
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

data CheckResult = CheckResult'
  { crModuleInfo :: ModuleInfo
  , crSource'    :: Source
  }

-- | Flattened unidirectional pattern for 'CheckResult' for destructuring inside
--   the 'ModuleInfo' field.
pattern CheckResult :: Interface -> [TCWarning] -> ModuleCheckMode -> Source -> CheckResult
pattern CheckResult { crInterface, crWarnings, crMode, crSource } <- CheckResult'
    { crModuleInfo = ModuleInfo
        { miInterface = crInterface
        , miWarnings = crWarnings
        , miMode = crMode
        }
    , crSource' = crSource
    }

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
  :: Mode
     -- ^ Should the file be type-checked, or only scope-checked?
  -> Source
     -- ^ The decorated source code.
  -> TCM CheckResult
typeCheckMain mode src = do
  -- liftIO $ putStrLn $ "This is typeCheckMain " ++ prettyShow f
  -- liftIO . putStrLn . show =<< getVerbosity

  -- For the main interface, we also remember the pragmas from the file
  setOptionsFromSourcePragmas src
  loadPrims <- optLoadPrimitives <$> pragmaOptions

  when loadPrims $ do
    reportSLn "import.main" 10 "Importing the primitive modules."
    libdirPrim <- liftIO getPrimitiveLibDir
    reportSLn "import.main" 20 $ "Library primitive dir = " ++ show libdirPrim
    -- Turn off import-chasing messages.
    -- We have to modify the persistent verbosity setting, since
    -- getInterface resets the current verbosity settings to the persistent ones.

    bracket_ (getsTC Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
      Lens.modifyPersistentVerbosity
        (Strict.Just . Trie.insert [] 0 . Strict.fromMaybe Trie.empty)
        -- set root verbosity to 0

      -- We don't want to generate highlighting information for Agda.Primitive.
      withHighlightingLevel None $
        forM_ (Set.map (libdirPrim </>) Lens.primitiveModules) $ \f -> do
          primSource <- parseSource (SourceFile $ mkAbsolute f)
          checkModuleName' (srcModuleName primSource) (srcOrigin primSource)
          void $ getNonMainInterface (srcModuleName primSource) (Just primSource)

    reportSLn "import.main" 10 $ "Done importing the primitive modules."

  -- Now do the type checking via getInterface.
  checkModuleName' (srcModuleName src) (srcOrigin src)

  mi <- getInterface (srcModuleName src) (MainInterface mode) (Just src)

  stCurrentModule `setTCLens'`
    Just ( iModuleName (miInterface mi)
         , iTopLevelModuleName (miInterface mi)
         )

  return $ CheckResult' mi src
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

-- | Check if the options used for checking an imported module are
--   compatible with the current options. Raises Non-fatal errors if
--   not.
checkOptionsCompatible ::
  PragmaOptions -> PragmaOptions -> TopLevelModuleName -> TCM Bool
checkOptionsCompatible current imported importedModule = flip execStateT True $ do
  reportSDoc "import.iface.options" 5 $ P.nest 2 $ "current options  =" P.<+> showOptions current
  reportSDoc "import.iface.options" 5 $ P.nest 2 $ "imported options =" P.<+> showOptions imported
  forM_ infectiveCoinfectiveOptions $ \opt -> do
    unless (icOptionOK opt current imported) $ do
      put False
      warning $
        (case icOptionKind opt of
           Infective   -> InfectiveImport
           Coinfective -> CoInfectiveImport)
        (icOptionWarning opt importedModule)
  where
  showOptions opts =
    P.prettyList $
    map (\opt -> (P.text (icOptionDescription opt) <> ": ") P.<+>
                 P.pretty (icOptionActive opt opts))
      infectiveCoinfectiveOptions

-- | Compare options and return collected warnings.
-- | Returns `Nothing` if warning collection was skipped.

getOptionsCompatibilityWarnings :: MainInterface -> Bool -> PragmaOptions -> Interface -> TCM (Maybe [TCWarning])
getOptionsCompatibilityWarnings isMain isPrim currentOptions i = runMaybeT $ exceptToMaybeT $ do
  -- We're just dropping these reasons-for-skipping messages for now.
  -- They weren't logged before, but they're nice for documenting the early returns.
  when isPrim $
    throwError "Options consistency checking disabled for always-available primitive module"
  whenM (lift $ checkOptionsCompatible currentOptions (iOptionsUsed i)
                  (iTopLevelModuleName i)) $
    throwError "No warnings to collect because options were compatible"
  lift $ getAllWarnings' isMain ErrorWarnings


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

  -- If any of the imports are newer we need to retype check
  badHashMessages <- fmap lefts $ forM (iImportedModules i) $ \(impName, impHash) -> runExceptT $ do
    reportSLn "import.iface" 30 $ concat ["Checking that module hash of import ", prettyShow impName, " matches ", prettyShow impHash ]
    latestImpHash <- lift $ lift $ setCurrentRange impName $ moduleHash impName
    reportSLn "import.iface" 30 $ concat ["Done checking module hash of import ", prettyShow impName]
    when (impHash /= latestImpHash) $
      throwError $ concat
        [ "module hash for imported module ", prettyShow impName, " is out of date"
        , " (import cached=", prettyShow impHash, ", latest=", prettyShow latestImpHash, ")"
        ]

  unlessNull badHashMessages (throwError . unlines)

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
      cleanCachedLog

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
      ho       <- getInteractionOutputCallback
      -- Every interface is treated in isolation. Note: Some changes to
      -- the persistent state may not be preserved if an error other
      -- than a type error or an IO exception is encountered in an
      -- imported module.
      (mi, newModToSource, newDecodedModules) <- (either throwError pure =<<) $
           withoutCache $
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
               setInteractionOutputCallback ho
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


-- | Formats and outputs the "Checking", "Finished" and "Loading " messages.

chaseMsg
  :: String               -- ^ The prefix, like @Checking@, @Finished@, @Loading @.
  -> TopLevelModuleName   -- ^ The module name.
  -> Maybe String         -- ^ Optionally: the file name.
  -> TCM ()
chaseMsg kind x file = do
  indentation <- (`replicate` ' ') <$> asksTC (pred . length . envImportPath)
  traceImports <- optTraceImports <$> commandLineOptions
  let maybeFile = caseMaybe file "." $ \ f -> " (" ++ f ++ ")."
      vLvl | kind == "Checking"
             && traceImports > 0 = 1
           | kind == "Finished"
             && traceImports > 1 = 1
           | List.isPrefixOf "Loading" kind
             && traceImports > 2 = 1
           | otherwise = 2
  reportSLn "import.chase" vLvl $ concat
    [ indentation, kind, " ", prettyShow x, maybeFile ]

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
  let x = mname
  let fp = filePath $ srcFilePath file
  let checkMsg = case isMain of
                   MainInterface ScopeCheck -> "Reading "
                   _                        -> "Checking"
      withMsgs = bracket_
       (chaseMsg checkMsg x $ Just fp)
       (const $ do ws <- getAllWarnings AllWarnings
                   let classified = classifyWarnings ws
                   let wa' = filter ((Strict.Just (Just mname) ==) .
                                     fmap rangeFileName . tcWarningOrigin) $
                             tcWarnings classified
                   unless (null wa') $
                     reportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> wa'
                   when (null (nonFatalErrors classified)) $ chaseMsg "Finished" x Nothing)

  withMsgs $
    Bench.billTo [Bench.TopModule mname] $
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

-- | Expert version of 'getAllWarnings'; if 'isMain' is a
-- 'MainInterface', the warnings definitely include also unsolved
-- warnings.

getAllWarnings' :: (MonadFail m, ReadTCState m, MonadWarning m, MonadTCM m) => MainInterface -> WhichWarnings -> m [TCWarning]
getAllWarnings' (MainInterface _) = getAllWarningsPreserving unsolvedWarnings
getAllWarnings' NotMainInterface  = getAllWarningsPreserving Set.empty

moduleHash :: TopLevelModuleName -> TCM Hash
moduleHash m = iFullHash <$> getNonMainInterface m Nothing
