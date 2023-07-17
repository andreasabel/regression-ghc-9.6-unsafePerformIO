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
runAgda backends = runTCMPrettyErrors $ do
  progName <- liftIO getProgName
  argv     <- liftIO getArgs
  let (Right (_bs, opts), warns) = runOptM $ parseBackendOptions backends argv defaultOptions
  Just inputFile <- liftIO $ mapM absolute $ optInputFile opts
  runAgdaWithOptions inputFile progName opts

-- | Run Agda with parsed command line options
runAgdaWithOptions
  :: AbsolutePath
  -> String             -- ^ program name
  -> CommandLineOptions -- ^ parsed command line options
  -> TCM ()
runAgdaWithOptions inputFile _progName opts = do
  setCommandLineOptions opts
  Imp.typeCheckMain Imp.TypeCheck =<< Imp.parseSource (SourceFile inputFile)
  return ()


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
