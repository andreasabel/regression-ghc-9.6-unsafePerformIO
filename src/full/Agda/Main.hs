{-# LANGUAGE CPP #-}

{-| Agda main module.
-}
module Agda.Main where

import Prelude hiding (null)

import qualified Control.Exception as E
import Control.Monad          ( void )
import Control.Monad.Except   ( MonadError(..), ExceptT(..), runExceptT )
import Control.Monad.IO.Class ( MonadIO(..) )

import qualified Data.List as List
import Data.Maybe

import System.Environment
import System.Exit
import System.Console.GetOpt
import qualified System.IO as IO

import Paths_Agda            ( getDataDir )

import Agda.Interaction.ExitCode (AgdaError(..), exitSuccess, exitAgdaWith)
import Agda.Interaction.Options
import Agda.Interaction.Options.Help (Help (..))
import Agda.Interaction.FindFile ( SourceFile(SourceFile) )
import qualified Agda.Interaction.Imports as Imp

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Pretty

import Agda.Compiler.Backend

import Agda.VersionCommit

import Agda.Utils.FileName (absolute, filePath, AbsolutePath)
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.String
import qualified Agda.Utils.Benchmark as UtilsBench

import Agda.Utils.Impossible

-- | The main function
runAgda :: [Backend] -> IO ()
runAgda = runAgda'

-- | The main function without importing built-in backends
runAgda' :: [Backend] -> IO ()
runAgda' backends = runTCMPrettyErrors $ do
  progName <- liftIO getProgName
  argv     <- liftIO getArgs
  let (z, warns) = runOptM $ parseBackendOptions backends argv defaultOptions
  mapM_ (warning . OptionWarning) warns
  conf     <- liftIO $ runExceptT $ do
    (bs, opts) <- ExceptT $ pure z
    -- The absolute path of the input file, if provided
    inputFile <- liftIO $ mapM absolute $ optInputFile opts
    mode      <- getMainMode bs inputFile opts
    return (bs, opts, mode)

  case conf of
    Right (bs, opts, MainModeRun interactor) -> do
          runAgdaWithOptions interactor progName opts

-- | Main execution mode
data MainMode
  = MainModeRun (Interactor ())

-- | Determine the main execution mode to run, based on the configured backends and command line options.
-- | This is pure.
getMainMode :: MonadError String m => [Backend] -> Maybe AbsolutePath -> CommandLineOptions -> m MainMode
getMainMode configuredBackends maybeInputFile opts
  | otherwise = do
      mi <- getInteractor configuredBackends maybeInputFile opts
      -- If there was no selection whatsoever (e.g. just invoked "agda"), we just show help and exit.
      return $ maybe undefined MainModeRun mi

type Interactor a
    -- Setup/initialization action.
    -- This is separated so that errors can be reported in the appropriate format.
    = TCM ()
    -- Type-checking action
    -> (AbsolutePath -> TCM CheckResult)
    -- Main transformed action.
    -> TCM a

data FrontendType
  = FrontEndEmacs
  | FrontEndJson
  | FrontEndRepl

-- The interactor to use when there are no frontends or backends specified.
defaultInteractor :: AbsolutePath -> Interactor ()
defaultInteractor file setup check = do setup; void $ check file

getInteractor :: MonadError String m => [Backend] -> Maybe AbsolutePath -> CommandLineOptions -> m (Maybe (Interactor ()))
getInteractor configuredBackends (Just inputFile) opts =
  return $ Just $ defaultInteractor inputFile

-- | Run Agda with parsed command line options
runAgdaWithOptions
  :: Interactor a       -- ^ Backend interaction
  -> String             -- ^ program name
  -> CommandLineOptions -- ^ parsed command line options
  -> TCM a
runAgdaWithOptions interactor progName opts = do
          -- Main function.
          -- Bill everything to root of Benchmark trie.
          UtilsBench.setBenchmarking UtilsBench.BenchmarkOn
            -- Andreas, Nisse, 2016-10-11 AIM XXIV
            -- Turn benchmarking on provisionally, otherwise we lose track of time spent
            -- on e.g. LaTeX-code generation.
            -- Benchmarking might be turned off later by setCommandlineOptions

          Bench.billTo [] $
            interactor initialSetup checkFile
          `finally_` do
            -- Print benchmarks.
            Bench.print

            -- Print accumulated statistics.
            printStatistics Nothing =<< useTC lensAccumStatistics
  where
    -- Options are fleshed out here so that (most) errors like
    -- "bad library path" are validated within the interactor,
    -- so that they are reported with the appropriate protocol/formatting.
    initialSetup :: TCM ()
    initialSetup = do
      opts <- addTrustedExecutables opts
      setCommandLineOptions opts

    checkFile :: AbsolutePath -> TCM CheckResult
    checkFile inputFile = do
        -- Andreas, 2013-10-30 The following 'resetState' kills the
        -- verbosity options.  That does not make sense (see fail/Issue641).
        -- 'resetState' here does not seem to serve any purpose,
        -- thus, I am removing it.
        -- resetState
          let mode = if optOnlyScopeChecking opts
                     then Imp.ScopeCheck
                     else Imp.TypeCheck

          result <- Imp.typeCheckMain mode =<< Imp.parseSource (SourceFile inputFile)

          unless (crMode result == ModuleScopeChecked) $
            unlessNullM (applyFlagsToTCWarnings (crWarnings result)) $ \ ws ->
              typeError $ NonFatalErrors ws

          let i = crInterface result
          reportSDoc "main" 50 $ pretty i

          -- Print accumulated warnings
          unlessNullM (tcWarnings . classifyWarnings <$> getAllWarnings AllWarnings) $ \ ws -> do
            let banner = text $ "\n" ++ delimiter "All done; warnings encountered"
            reportSDoc "warning" 1 $
              vcat $ punctuate "\n" $ banner : (prettyTCM <$> ws)

          return result



-- | Run a TCM action in IO; catch and pretty print errors.

-- If some error message cannot be printed due to locale issues, then
-- one may get the "Error when handling error" error message. There is
-- currently no test case for this error, but on some systems one can
-- (at the time of writing) trigger it by running @LC_CTYPE=C agda
-- --no-libraries Bug.agda@, where @Bug.agda@ contains the following
-- code (if there is some other file in the same directory, for
-- instance @Bug.lagda@, then the error message may be different):
--
-- @
-- _ : Set
-- _ = Set
-- @

runTCMPrettyErrors :: TCM () -> IO ()
runTCMPrettyErrors tcm = do
  r <- runTCMTop
    ( ( (Nothing <$ tcm)
          `catchError` \err -> do
            s2s <- prettyTCWarnings' =<< getAllWarningsOfTCErr err
            s1  <- prettyError err
            let ss = filter (not . null) $ s2s ++ [s1]
            unless (null s1) (liftIO $ putStr $ unlines ss)
            return (Just TCMError)
      ) `catchImpossible` \e -> do
          liftIO $ putStr $ E.displayException e
          return (Just ImpossibleError)
    ) `E.catches`
        -- Catch all exceptions except for those of type ExitCode
        -- (which are thrown by exitWith) and asynchronous exceptions
        -- (which are for instance raised when Ctrl-C is used, or if
        -- the program runs out of heap or stack space).
        [ E.Handler $ \(e :: ExitCode)         -> E.throw e
        , E.Handler $ \(e :: E.AsyncException) -> E.throw e
        , E.Handler $ \(e :: E.SomeException)  -> do
            liftIO $ putStr $ E.displayException e
            return $ Right (Just UnknownError)
        ]
  case r of
    Right Nothing       -> exitSuccess
    Right (Just reason) -> exitAgdaWith reason
    Left err            -> do
      liftIO $ do
        putStrLn "\n\nError when handling error:"
        putStrLn $ tcErrString err
      exitAgdaWith UnknownError
