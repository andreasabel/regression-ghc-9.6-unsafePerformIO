-- {-# OPTIONS_GHC -Wall #-}

{-| Agda main module.
-}
module Agda.Main where

import qualified Control.Exception as E

import Control.Monad.Except   ( MonadError(..) )
import Control.Monad.IO.Class ( MonadIO(..) )

import System.Environment
import System.Exit

import Agda.Interaction.ExitCode (AgdaError(..), exitAgdaWith)
import Agda.Interaction.Options
import Agda.Interaction.FindFile ( SourceFile(SourceFile) )
import Agda.Interaction.Imports  ( typeCheckMain, parseSource )

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors

import Agda.Utils.FileName (absolute, AbsolutePath)
import Agda.Utils.Monad

import Agda.Utils.Impossible

-- | The main function
runAgda :: [a] -> IO ()
runAgda _backends =
  runTCMPrettyErrors $ do
    argv <- liftIO getArgs
    let (Right opts, _warns) = runOptM $ getOptSimple (stripRTS argv) standardOptions inputFlag defaultOptions
    Just inputFile <- liftIO $ mapM absolute $ optInputFile opts
    runAgdaWithOptions inputFile opts

-- | Run Agda with parsed command line options
runAgdaWithOptions
  :: AbsolutePath
  -> CommandLineOptions -- ^ parsed command line options
  -> TCM ()
runAgdaWithOptions inputFile opts = do
  setCommandLineOptions opts
  typeCheckMain =<< parseSource (SourceFile inputFile)


-- | Run a TCM action in IO; catch and pretty print errors.
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
