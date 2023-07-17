
-- | Reconstruct dropped parameters from constructors.  Used by
--   with-abstraction to avoid ill-typed abstractions (#745). Note that the
--   term is invalid after parameter reconstruction. Parameters need to be
--   dropped again before using it.

module Agda.TypeChecking.ReconstructParameters where

import Data.Functor ( ($>) )
import Data.Maybe

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Datatypes

import Agda.Utils.Size
import Agda.Utils.Either
import Agda.Utils.Function (applyWhen)

import Agda.Utils.Impossible

reconstructParametersInType :: Type -> TCM Type
reconstructParametersInType = return

reconstructParametersInTel :: Telescope -> TCM Telescope
reconstructParametersInTel EmptyTel = return EmptyTel
reconstructParametersInTel (ExtendTel a tel) = do
  ar <- reconstructParametersInType (unDom a)
  addContext (absName tel, a) $
    ExtendTel (ar <$ a) <$> traverse reconstructParametersInTel tel

reconstructParametersInEqView :: EqualityView -> TCM EqualityView
reconstructParametersInEqView (EqualityType s eq l a u v) =
  EqualityType s eq l <$> traverse (reconstructParameters $ sort s) a
                      <*> traverse (reconstructParameters $ El s $ unArg a) u
                      <*> traverse (reconstructParameters $ El s $ unArg a) v
reconstructParametersInEqView (OtherType a) = OtherType <$> reconstructParametersInType a
reconstructParametersInEqView (IdiomType a) = IdiomType <$> reconstructParametersInType a

reconstructParameters :: Type -> Term -> TCM Term
reconstructParameters _ = return

reconstruct :: Type -> Term -> TCM Term
reconstruct ty = return
-- Extract the parameters from the type of a constructor
-- application or the type of the principal argument of a
-- projection.
extractParameters :: QName -> Type -> TCM Args
extractParameters q ty = undefined

dropParameters :: TermLike a => a -> TCM a
dropParameters = traverseTermM $
    \case
        Con c ci vs -> do
          Constructor{ conData = d } <- theDef <$> getConstInfo (conName c)
          Just n <- defParameters <$> getConstInfo d
          return $ Con c ci $ drop n vs
        v@(Def f vs) -> do
          isRelevantProjection f >>= \case
            Nothing -> return v
            Just pr -> return $ applyE (projDropPars pr ProjSystem) vs
        v -> return v
