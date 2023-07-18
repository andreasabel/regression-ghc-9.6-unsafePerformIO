-- | Wrapper for "Agda.Main".
--
-- Agda is installed as a library. This module is used to build the
-- executable.
{-# OPTIONS_GHC -Wall #-}

module Main (main) where

import qualified Control.Exception as E

import Control.Monad.Except   ( MonadError(..) )
import Control.Monad.IO.Class ( MonadIO(..) )

import System.Exit

import Agda.Interaction.ExitCode (AgdaError(..), exitAgdaWith)
import Agda.Interaction.Options.Base (defaultPragmaOptions, lensOptVerbose, parseVerboseKey)

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad (TCM, runTCMTop)
import Agda.TypeChecking.Monad.Options ( setPragmaOptions )

import Agda.Utils.Monad
-- import Agda.Utils.Null (empty)
import Agda.Utils.Lens
import qualified Agda.Utils.Maybe.Strict as Strict
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.Impossible
import Agda.ImpossibleTest (impossibleTestReduceM)

main :: IO ()
main = runTCMPrettyErrors $ do

    let verb = Strict.Just $ Trie.singleton (parseVerboseKey "impossible") 10
    setPragmaOptions $ set lensOptVerbose verb defaultPragmaOptions

    let msg = words "ReduceM SHOULD ALSO PRINT THIS DEBUG MESSAGE!!!!!!!!!!!!! LET'S MAKE IT VERY LONG SO IT CANNOT BE OVERLOOKED!!!!!!!!!!!!!!!!!!!"
    impossibleTestReduceM msg

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
