-- | Wrapper for "Agda.Main".
--
-- Agda is installed as a library. This module is used to build the
-- executable.
{-# OPTIONS_GHC -Wall #-}

module Main (main) where

import qualified Control.Exception as E

import Control.Monad          ( (<=<) )
import Control.Monad.Except   ( MonadError(..) )
import Control.Monad.IO.Class ( MonadIO(..) )

import Data.IORef (newIORef)

import Agda.Interaction.Options.Base (defaultPragmaOptions, lensOptVerbose, parseVerboseKey)

import Agda.TypeChecking.Errors (prettyError)
import Agda.TypeChecking.Monad (TCM, initEnv, initState, unTCM)
import Agda.TypeChecking.Monad.Options ( setPragmaOptions )

import Agda.TypeChecking.Monad.Base   ( TCM, ReduceM, runReduceM )
import Agda.TypeChecking.Monad.Debug  ( MonadDebug, __IMPOSSIBLE_VERBOSE__ )
import Agda.TypeChecking.Reduce.Monad ()

import Agda.Utils.CallStack           ( HasCallStack )
import Agda.Utils.Impossible          ( __IMPOSSIBLE__ )

-- import Agda.Utils.Monad
-- import Agda.Utils.Null (empty)
import Agda.Utils.Lens
import qualified Agda.Utils.Maybe.Strict as Strict
import qualified Agda.Utils.Trie as Trie

-- import Agda.Utils.Impossible
-- import Agda.ImpossibleTest (impossibleTestReduceM)

main :: IO ()
main = runTCMPrettyErrors $ do

    let verb = Strict.Just $ Trie.singleton (parseVerboseKey "impossible") 10
    setPragmaOptions $ set lensOptVerbose verb defaultPragmaOptions

    let msg = words "ReduceM SHOULD ALSO PRINT THIS DEBUG MESSAGE!!!!!!!!!!!!! LET'S MAKE IT VERY LONG SO IT CANNOT BE OVERLOOKED!!!!!!!!!!!!!!!!!!!"
    impossibleTestReduceM msg

-- | Run a TCM action in IO; catch and pretty print errors.
runTCMPrettyErrors :: TCM () -> IO ()
runTCMPrettyErrors m = do
    r <- liftIO $ newIORef initState
    unTCM (catchError m $ (liftIO . putStr) <=< prettyError) r initEnv

impossibleTestReduceM :: (HasCallStack) => [String] -> TCM a
impossibleTestReduceM = runReduceM . \case
  []   -> __IMPOSSIBLE__
  strs -> __IMPOSSIBLE_VERBOSE__ $ unwords strs
