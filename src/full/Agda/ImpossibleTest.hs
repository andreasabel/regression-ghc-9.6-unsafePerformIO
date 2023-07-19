-- | Facility to test throwing internal errors.

module Agda.ImpossibleTest where

import Agda.TypeChecking.Monad.Base   ( TCM, ReduceM, runReduceM )
import Agda.TypeChecking.Monad.Debug  ( __IMPOSSIBLE_VERBOSE__ )
import Agda.TypeChecking.Reduce.Monad () -- instance MonadDebug ReduceM

import GHC.Stack                      ( HasCallStack )

impossibleTestReduceM :: (HasCallStack) => [String] -> TCM a
impossibleTestReduceM = runReduceM . __IMPOSSIBLE_VERBOSE__ . unwords
