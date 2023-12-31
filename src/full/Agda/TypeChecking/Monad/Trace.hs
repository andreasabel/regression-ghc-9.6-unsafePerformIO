
module Agda.TypeChecking.Monad.Trace where

import Prelude hiding (null)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Identity
import Control.Monad.Writer

import qualified Data.Set as Set

import Agda.Syntax.Position
import qualified Agda.Syntax.Position as P

import Agda.TypeChecking.Monad.Base
  hiding (ModuleInfo, MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.State

import Agda.Utils.Function

import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (prettyShow)

---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

interestingCall :: Call -> Bool
interestingCall _ = True

class (MonadTCEnv m, ReadTCState m) => MonadTrace m where

  -- | Record a function call in the trace.
  traceCall :: Call -> m a -> m a
  traceCall call m = do
    cl <- buildClosure call
    traceClosureCall cl m

  traceCallM :: m Call -> m a -> m a
  traceCallM call m = flip traceCall m =<< call

  -- | Reset 'envCall' to previous value in the continuation.
  --
  -- Caveat: if the last 'traceCall' did not set an 'interestingCall',
  -- for example, only set the 'Range' with 'SetRange',
  -- we will revert to the last interesting call.
  traceCallCPS :: Call -> ((a -> m b) -> m b) -> ((a -> m b) -> m b)
  traceCallCPS call k ret = do
    mcall <- asksTC envCall
    traceCall call $ k $ \ a -> do
      maybe id traceClosureCall mcall $ ret a

  traceClosureCall :: Closure Call -> m a -> m a

instance MonadTrace m => MonadTrace (IdentityT m) where
  traceClosureCall c f = IdentityT $ traceClosureCall c $ runIdentityT f

instance MonadTrace m => MonadTrace (ReaderT r m) where
  traceClosureCall c f = ReaderT $ \r -> traceClosureCall c $ runReaderT f r

instance MonadTrace m => MonadTrace (StateT s m) where
  traceClosureCall c f = StateT (traceClosureCall c . runStateT f)

instance (MonadTrace m, Monoid w) => MonadTrace (WriterT w m) where
  traceClosureCall c f = WriterT $ traceClosureCall c $ runWriterT f

instance MonadTrace m => MonadTrace (ExceptT e m) where
  traceClosureCall c f = ExceptT $ traceClosureCall c $ runExceptT f

instance MonadTrace TCM where
  traceClosureCall cl m = do
    -- Andreas, 2016-09-13 issue #2177
    -- Since the fix of #2092 we may report an error outside the current file.
    -- (For instance, if we import a module which then happens to have the
    -- wrong name.)
    -- Thus, we no longer crash, but just report the alien range.
    -- -- Andreas, 2015-02-09 Make sure we do not set a range
    -- -- outside the current file
    verboseS "check.ranges" 90 $
      Strict.whenJust (rangeFile callRange) $ \f -> do
        currentFile <- asksTC envCurrentPath
        when (currentFile /= Just (rangeFilePath f)) $ do
          reportSLn "check.ranges" 90 $
            prettyShow call ++
            " is setting the current range to " ++ show callRange ++
            " which is outside of the current file " ++ show currentFile

    -- Compute update to 'Range' and 'Call' components of 'TCEnv'.
    let withCall = localTC $ foldr (.) id $ concat $
          [ [ \e -> e { envCall = Just cl } | interestingCall call ]
          , [ \e -> e { envHighlightingRange = callRange }
            | callHasRange && highlightCall
              || isNoHighlighting
            ]
          , [ \e -> e { envRange = callRange } | callHasRange ]
          ]

    -- For interactive highlighting, also wrap computation @m@ in 'highlightAsTypeChecked':
    ifNotM (pure highlightCall `and2M` do (Interactive ==) . envHighlightingLevel <$> askTC)
      {-then-} (withCall m)
      {-else-} $ do
        oldRange <- envHighlightingRange <$> askTC
        highlightAsTypeChecked oldRange callRange $
          withCall m
    where
    call = clValue cl
    callRange = getRange call
    callHasRange = not $ null callRange

    -- Should the given call trigger interactive highlighting?
    highlightCall = True
    isNoHighlighting = case call of
      NoHighlighting{} -> True
      _ -> False

getCurrentRange :: MonadTCEnv m => m Range
getCurrentRange = asksTC envRange

-- | Sets the current range (for error messages etc.) to the range
--   of the given object, if it has a range (i.e., its range is not 'noRange').
setCurrentRange :: (MonadTrace m, HasRange x) => x -> m a -> m a
setCurrentRange x = applyUnless (null r) $ traceCall $ SetRange r
  where r = getRange x

-- | @highlightAsTypeChecked rPre r m@ runs @m@ and returns its
--   result. Additionally, some code may be highlighted:
--
-- * If @r@ is non-empty and not a sub-range of @rPre@ (after
--   'P.continuousPerLine' has been applied to both): @r@ is
--   highlighted as being type-checked while @m@ is running (this
--   highlighting is removed if @m@ completes /successfully/).
--
-- * Otherwise: Highlighting is removed for @rPre - r@ before @m@
--   runs, and if @m@ completes successfully, then @rPre - r@ is
--   highlighted as being type-checked.

highlightAsTypeChecked
  :: (MonadTrace m)
  => Range   -- ^ @rPre@
  -> Range   -- ^ @r@
  -> m a
  -> m a
highlightAsTypeChecked rPre r m = m
