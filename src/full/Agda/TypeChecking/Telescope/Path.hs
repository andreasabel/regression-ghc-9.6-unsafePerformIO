{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.Telescope.Path where

import Prelude hiding (null)

import qualified Data.List as List
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Size

import Agda.Utils.Impossible


-- | In an ambient context Γ, @telePiPath f lams Δ t bs@ builds a type that
-- can be @telViewPathBoundaryP'ed@ into (TelV Δ t, bs').
--   Γ.Δ ⊢ t
--   bs = [(i,u_i)]
--   Δ = Δ0,(i : I),Δ1
--   ∀ b ∈ {0,1}.  Γ.Δ0 | lams Δ1 (u_i .b) : (telePiPath f Δ1 t bs)(i = b) -- kinda: see lams
--   Γ ⊢ telePiPath f Δ t bs
telePiPath :: (Abs Type -> Abs Type) -> ([Arg ArgName] -> Term -> Term) -> Telescope -> Type -> Boundary -> TCM Type
telePiPath reAbs lams tel t bs = undefined

-- | @telePiPath_ Δ t [(i,u)]@
--   Δ ⊢ t
--   i ∈ Δ
--   Δ ⊢ u_b : t  for  b ∈ {0,1}
telePiPath_ :: Telescope -> Type -> [(Int,(Term,Term))] -> TCM Type
telePiPath_ tel t bndry = do
  reportSDoc "tc.tel.path" 40                  $ text "tel  " <+> prettyTCM tel
  reportSDoc "tc.tel.path" 40 $ addContext tel $ text "type " <+> prettyTCM t
  reportSDoc "tc.tel.path" 40 $ addContext tel $ text "bndry" <+> pretty bndry

  telePiPath id argsLam tel t [(var i, u) | (i , u) <- bndry]
 where
   argsLam args tm = strengthenS impossible 1 `applySubst`
     foldr (\ Arg{argInfo = ai, unArg = x} -> Lam ai . Abs x) tm args

-- | arity of the type, including both Pi and Path.
--   Does not reduce the type.
arityPiPath :: Type -> TCM Int
arityPiPath t = do
  piOrPath t >>= \case
    Left (_, u) -> (+1) <$> arityPiPath (unAbs u)
    Right _     -> return 0

-- | Collect the interval copattern variables as list of de Bruijn indices.
class IApplyVars p where
  iApplyVars :: p -> [Int]

instance DeBruijn a => IApplyVars (Pattern' a) where
  iApplyVars = \case
    IApplyP _ t u x -> [ fromMaybe __IMPOSSIBLE__ $ deBruijnView x ]
    VarP{}          -> []
    ProjP{}         -> []
    LitP{}          -> []
    DotP{}          -> []
    DefP _ _ ps     -> iApplyVars ps
    ConP _ _ ps     -> iApplyVars ps

instance IApplyVars p => IApplyVars (NamedArg p) where
  iApplyVars = iApplyVars . namedArg

instance IApplyVars p => IApplyVars [p] where
  iApplyVars = concatMap iApplyVars

-- | Check whether a type is the built-in interval type.
isInterval :: (MonadTCM m, MonadReduce m) => Type -> m Bool
isInterval t = return False
