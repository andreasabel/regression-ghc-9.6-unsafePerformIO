{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Constraints where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except

import qualified Data.List as List
import qualified Data.Set as Set
import Data.Either

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.LevelConstraints
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Sort
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Warnings

import Agda.TypeChecking.Irrelevance
import {-# SOURCE #-} Agda.TypeChecking.Rules.Term
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars

import Agda.Utils.CallStack ( withCurrentCallStack )
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.ProfileOptions as Profile

import Agda.Utils.Impossible

instance MonadConstraint TCM where
  addConstraint             = addConstraintTCM
  addAwakeConstraint        = addAwakeConstraint'
  solveConstraint           = solveConstraintTCM
  solveSomeAwakeConstraints = solveSomeAwakeConstraintsTCM
  wakeConstraints           = wakeConstraintsTCM
  stealConstraints          = stealConstraintsTCM
  modifyAwakeConstraints    = modifyTC . mapAwakeConstraints
  modifySleepingConstraints = modifyTC . mapSleepingConstraints

addConstraintTCM :: Blocker -> Constraint -> TCM ()
addConstraintTCM unblock c = do
      pids <- asksTC envActiveProblems
      reportSDoc "tc.constr.add" 20 $ hsep
        [ "adding constraint"
        , prettyTCM . PConstr pids unblock =<< buildClosure c
        , "unblocker: " , prettyTCM unblock
        ]
      -- Jesper, 2022-10-22: We should never block on a meta that is
      -- already solved.
      forM_ (Set.toList $ allBlockingMetas unblock) $ \m ->
        whenM (isInstantiatedMeta m) $ do
          reportSDoc "tc.constr.add" 5 $ "Attempted to block on solved meta" <+> prettyTCM m
          __IMPOSSIBLE__
      -- Need to reduce to reveal possibly blocking metas
      c <- reduce =<< instantiateFull c
      caseMaybeM (simpl c) {-no-} (addConstraint' unblock c) $ {-yes-} \ cs -> do
          reportSDoc "tc.constr.add" 20 $ "  simplified:" <+> prettyList (map prettyTCM cs)
          mapM_ solveConstraint_ cs
      -- The added constraint can cause instance constraints to be solved,
      -- but only the constraints which aren’t blocked on an uninstantiated meta.
      unless (isInstanceConstraint c) $
         wakeConstraints' isWakeableInstanceConstraint
    where
      isWakeableInstanceConstraint :: ProblemConstraint -> WakeUp
      isWakeableInstanceConstraint c =
        case clValue $ theConstraint c of
          FindInstance{}
            | constraintUnblocker c == alwaysUnblock -> WakeUp
          _ -> DontWakeUp Nothing

      isLvl LevelCmp{} = True
      isLvl _          = False

      -- Try to simplify a level constraint
      simpl :: Constraint -> TCM (Maybe [Constraint])
      simpl c
        | isLvl c = do
          -- Get all level constraints.
          lvlcs <- instantiateFull =<< do
            List.filter (isLvl . clValue) . map theConstraint <$> getAllConstraints
          unless (null lvlcs) $ do
            reportSDoc "tc.constr.lvl" 40 $ vcat
              [ "simplifying level constraint" <+> prettyTCM c
              , nest 2 $ hang "using" 2 $ prettyTCM lvlcs
              ]
          -- Try to simplify @c@ using the other constraints.
          return $ simplifyLevelConstraint c $ map clValue lvlcs
        | otherwise = return Nothing

wakeConstraintsTCM :: (ProblemConstraint-> WakeUp) -> TCM ()
wakeConstraintsTCM wake = do
  c <- useR stSleepingConstraints
  let (wakeup, sleepin) = partitionEithers $ map checkWakeUp c
  reportSLn "tc.constr.wake" 50 $
    "waking up         " ++ show (List.map (Set.toList . constraintProblems) wakeup) ++ "\n" ++
    "  still sleeping: " ++ show (List.map (Set.toList . constraintProblems) sleepin)
  modifySleepingConstraints $ const sleepin
  modifyAwakeConstraints (++ wakeup)
  where
    checkWakeUp c = case wake c of
      WakeUp              -> Left c
      DontWakeUp Nothing  -> Right c
      DontWakeUp (Just u) -> Right c{ constraintUnblocker = u }

-- | Add all constraints belonging to the given problem to the current problem(s).
stealConstraintsTCM :: ProblemId -> TCM ()
stealConstraintsTCM pid = do
  current <- asksTC envActiveProblems
  reportSLn "tc.constr.steal" 50 $ "problem " ++ show (Set.toList current) ++ " is stealing problem " ++ show pid ++ "'s constraints!"
  -- Add current to any constraint in pid.
  let rename pc@(PConstr pids u c) | Set.member pid pids = PConstr (Set.union current pids) u c
                                   | otherwise           = pc
  -- We should never steal from an active problem.
  whenM (Set.member pid <$> asksTC envActiveProblems) __IMPOSSIBLE__
  modifyAwakeConstraints    $ List.map rename
  modifySleepingConstraints $ List.map rename


-- | Don't allow the argument to produce any blocking constraints.
--
-- WARNING: this does not mean that the given computation cannot
-- constrain the solution space further.
-- It can well do so, by solving metas.
noConstraints
  :: (MonadConstraint m, MonadWarning m, MonadError TCErr m, MonadFresh ProblemId m)
  => m a -> m a
noConstraints problem = do
  (pid, x) <- newProblem problem
  cs <- getConstraintsForProblem pid
  unless (null cs) $ do
    withCurrentCallStack $ \loc -> do
      w <- warning'_ loc (UnsolvedConstraints cs)
      typeError' loc $ NonFatalErrors [ w ]
  return x

-- | Run a computation that should succeeds without constraining
--   the solution space, i.e., not add any information about meta-variables.
nonConstraining ::
  ( HasOptions m
  , MonadConstraint m
  , MonadDebug m
  , MonadError TCErr m
  , MonadFresh ProblemId m
  , MonadTCEnv m
  , MonadWarning m
  ) => m a -> m a
nonConstraining = dontAssignMetas . noConstraints

-- | Create a fresh problem for the given action.
newProblem
  :: (MonadFresh ProblemId m, MonadConstraint m)
  => m a -> m (ProblemId, a)
newProblem action = do
  pid <- fresh
  -- Don't get distracted by other constraints while working on the problem
  x <- nowSolvingConstraints $ solvingProblem pid action
  -- Now we can check any woken constraints
  solveAwakeConstraints
  return (pid, x)

newProblem_
  :: (MonadFresh ProblemId m, MonadConstraint m)
  => m a -> m ProblemId
newProblem_ action = fst <$> newProblem action

ifNoConstraints :: TCM a -> (a -> TCM b) -> (ProblemId -> a -> TCM b) -> TCM b
ifNoConstraints check ifNo ifCs = do
  (pid, x) <- newProblem check
  ifM (isProblemSolved pid) (ifNo x) (ifCs pid x)

ifNoConstraints_ :: TCM () -> TCM a -> (ProblemId -> TCM a) -> TCM a
ifNoConstraints_ check ifNo ifCs = ifNoConstraints check (const ifNo) (\pid _ -> ifCs pid)

-- | @guardConstraint c blocker@ tries to solve @blocker@ first.
--   If successful without constraints, it moves on to solve @c@, otherwise it
--   adds a @c@ to the constraint pool, blocked by the problem generated by @blocker@.
guardConstraint :: Constraint -> TCM () -> TCM ()
guardConstraint c blocker =
  ifNoConstraints_ blocker (solveConstraint c) (\ pid -> addConstraint (unblockOnProblem pid) c)

whenConstraints :: TCM () -> TCM () -> TCM ()
whenConstraints action handler =
  ifNoConstraints_ action (return ()) $ \pid -> do
    stealConstraints pid
    handler

-- | Wake up the constraints depending on the given meta.
wakeupConstraints :: MonadMetaSolver m => MetaId -> m ()
wakeupConstraints x = do
  wakeConstraints' (wakeIfBlockedOnMeta x . constraintUnblocker)
  solveAwakeConstraints

-- | Wake up all constraints not blocked on a problem.
wakeupConstraints_ :: TCM ()
wakeupConstraints_ = do
  wakeConstraints' (wakeup . constraintUnblocker)
  solveAwakeConstraints
  where
    wakeup u | Set.null $ allBlockingProblems u = WakeUp
             | otherwise                        = DontWakeUp Nothing

-- | Solve awake constraints matching the predicate. If the second argument is
--   True solve constraints even if already 'isSolvingConstraints'.
solveSomeAwakeConstraintsTCM :: (ProblemConstraint -> Bool) -> Bool -> TCM ()
solveSomeAwakeConstraintsTCM solveThis force = do
    whenProfile Profile.Constraints $ liftTCM $ tickMax "max-open-constraints" . List.genericLength =<< getAllConstraints
    whenM ((force ||) . not <$> isSolvingConstraints) $ nowSolvingConstraints $ do
     -- solveSizeConstraints -- Andreas, 2012-09-27 attacks size constrs too early
     -- Ulf, 2016-12-06: Don't inherit problems here! Stored constraints
     -- already contain all their dependencies.
     locallyTC eActiveProblems (const Set.empty) solve
  where
    solve = do
      reportSDoc "tc.constr.solve" 10 $ hsep [ "Solving awake constraints."
                                             , text . show . length =<< getAwakeConstraints
                                             , "remaining." ]
      whenJustM (takeAwakeConstraint' solveThis) $ \ c -> do
        withConstraint solveConstraint c
        solve

solveConstraintTCM :: Constraint -> TCM ()
solveConstraintTCM c = do
    whenProfile Profile.Constraints $ liftTCM $ tick "attempted-constraints"
    verboseBracket "tc.constr.solve" 20 "solving constraint" $ do
      pids <- asksTC envActiveProblems
      reportSDoc "tc.constr.solve.constr" 20 $ text (show $ Set.toList pids) <+> prettyTCM c
      solveConstraint_ c

solveConstraint_ :: Constraint -> TCM ()
solveConstraint_ _ = return ()

checkTypeCheckingProblem :: TypeCheckingProblem -> TCM Term
checkTypeCheckingProblem _ = undefined

debugConstraints :: TCM ()
debugConstraints = verboseS "tc.constr" 50 $ do
  awake    <- useTC stAwakeConstraints
  sleeping <- useTC stSleepingConstraints
  reportSDoc "tc.constr" 50 $ vcat
    [ "Current constraints"
    , nest 2 $ vcat [ "awake " <+> vcat (map prettyTCM awake)
                    , "asleep" <+> vcat (map prettyTCM sleeping) ] ]

-- Update the blocker after some instantiation or pruning might have happened.
updateBlocker :: (PureTCM m) => Blocker -> m Blocker
updateBlocker b = case b of
  UnblockOnAll xs -> unblockOnAll . Set.fromList <$> traverse updateBlocker (Set.toList xs)
  UnblockOnAny xs -> unblockOnAny . Set.fromList <$> traverse updateBlocker (Set.toList xs)
  UnblockOnMeta x -> ifM (isInstantiatedMeta x) (return alwaysUnblock) (return b)
  UnblockOnProblem pi -> ifM (isProblemSolved pi) (return alwaysUnblock) (return $ UnblockOnProblem pi)
  UnblockOnDef qn -> return (unblockOnDef qn)

addAndUnblocker :: (PureTCM m, MonadBlock m) => Blocker -> m a -> m a
addAndUnblocker u
  | u == alwaysUnblock = id
  | otherwise          = catchPatternErr $ \ u' -> do
      u <- updateBlocker u
      patternViolation (unblockOnBoth u u')

addOrUnblocker :: (PureTCM m, MonadBlock m) => Blocker -> m a -> m a
addOrUnblocker u
  | u == neverUnblock = id
  | otherwise         = catchPatternErr $ \ u' -> do
      u <- updateBlocker u
      patternViolation (unblockOnEither u u')

-- Reduce a term and call the continuation. If the continuation is
-- blocked, the whole call is blocked either on what blocked the reduction
-- or on what blocked the continuation (using `blockedOnEither`).
withReduced
  :: (Reduce a, IsMeta a, PureTCM m, MonadBlock m)
  => a -> (a -> m b) -> m b
withReduced a cont = ifBlocked a (\b a' -> addOrUnblocker b $ cont a') (\_ a' -> cont a')
