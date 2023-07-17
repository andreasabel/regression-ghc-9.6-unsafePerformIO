{-# LANGUAGE NondecreasingIndentation   #-}

module Agda.TypeChecking.Rules.Record where

import Prelude hiding (null, not, (&&), (||))

import Control.Monad
import Data.Maybe
import qualified Data.Set as Set

import Agda.Interaction.Options

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Rewriting.Confluence
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.CompiledClause (hasProjectionPatterns)
import Agda.TypeChecking.CompiledClause.Compile
import Agda.TypeChecking.Rules.Term ( isType_ )

import Agda.Utils.Boolean
import Agda.Utils.Function ( applyWhen )
import Agda.Utils.List (headWithDefault)
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.POMonoid
import Agda.Utils.Pretty (render)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size
import Agda.Utils.WithDefault

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

-- | @checkRecDef i name con ps contel fields@
--
--     [@name@]    Record type identifier.
--
--     [@con@]     Maybe constructor name and info.
--
--     [@ps@]      Record parameters.
--
--     [@contel@]  Approximate type of constructor (@fields@ -> dummy).
--                 Does not include record parameters.
--
--     [@fields@]  List of field signatures.
--
checkRecDef
  :: A.DefInfo                 -- ^ Position and other info.
  -> QName                     -- ^ Record type identifier.
  -> UniverseCheck             -- ^ Check universes?
  -> A.RecordDirectives        -- ^ (Co)Inductive, (No)Eta, (Co)Pattern, Constructor?
  -> A.DataDefParams           -- ^ Record parameters.
  -> A.Expr                    -- ^ Approximate type of constructor (@fields@ -> dummy).
                               --   Does not include record parameters.
  -> [A.Field]                 -- ^ Field signatures.
  -> TCM ()
checkRecDef i name uc (RecordDirectives ind eta0 pat con) (A.DataDefParams gpars ps) contel0 fields = return ()

addCompositionForRecord
  :: QName       -- ^ Datatype name.
  -> EtaEquality
  -> ConHead
  -> Telescope   -- ^ @Γ@ parameters.
  -> [Arg QName] -- ^ Projection names.
  -> Telescope   -- ^ @Γ ⊢ Φ@ field types.
  -> Type        -- ^ @Γ ⊢ T@ target type.
  -> TCM ()
addCompositionForRecord name eta con tel fs ftel rect = return ()
defineCompKitR ::
    QName          -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM CompKit
defineCompKitR name params fsT fns rect = do
  required <- mapM getTerm'
        [ someBuiltin builtinInterval
        , someBuiltin builtinIZero
        , someBuiltin builtinIOne
        , someBuiltin builtinIMin
        , someBuiltin builtinIMax
        , someBuiltin builtinINeg
        , someBuiltin builtinPOr
        , someBuiltin builtinItIsOne
        ]
  reportSDoc "tc.rec.cxt" 30 $ prettyTCM params
  reportSDoc "tc.rec.cxt" 30 $ prettyTCM fsT
  reportSDoc "tc.rec.cxt" 30 $ pretty rect
  return emptyCompKit
  where
    whenDefined xs m = do
      xs <- mapM getTerm' xs
      if all isJust xs then m else return Nothing


defineKanOperationR
  :: Command
  -> QName       -- ^ some name, e.g. record name
  -> Telescope   -- ^ param types Δ
  -> Telescope   -- ^ fields' types Δ ⊢ Φ
  -> [Arg QName] -- ^ fields' names
  -> Type        -- ^ record type Δ ⊢ T
  -> TCM (Maybe QName)
defineKanOperationR cmd name params fsT fns rect = return Nothing

{-| @checkRecordProjections m r q tel ftel fs@.

    [@m@    ]  name of the generated module

    [@r@    ]  name of the record type

    [@con@  ]  name of the record constructor

    [@tel@  ]  parameters (perhaps erased) and record variable r ("self")

    [@ftel@ ]  telescope of fields

    [@fs@   ]  the fields to be checked
-}
checkRecordProjections ::
  ModuleName -> QName -> Bool -> ConHead -> Telescope -> Telescope ->
  [A.Declaration] -> TCM ()
checkRecordProjections m r hasNamedCon con tel ftel fs = do
    checkProjs EmptyTel ftel [] fs
  where

    checkProjs :: Telescope -> Telescope -> [Term] -> [A.Declaration] -> TCM ()

    checkProjs _ _ _ [] = return ()

    checkProjs ftel1 ftel2 vs (A.ScopedDecl scope fs' : fs) =
      setScope scope >> checkProjs ftel1 ftel2 vs (fs' ++ fs)

    -- Case: projection.
    checkProjs ftel1 (ExtendTel (dom@Dom{domInfo = ai,unDom = t}) ftel2) vs (A.Field info x _ : fs) =
      traceCall (CheckProjection (getRange info) x t) $ do
      -- Andreas, 2012-06-07:
      -- Issue 387: It is wrong to just type check field types again
      -- because then meta variables are created again.
      -- Instead, we take the field type t from the field telescope.
      reportSDoc "tc.rec.proj" 5 $ sep
        [ "checking projection" <+> prettyTCM x
        , nest 2 $ vcat
          [ "top   =" <+> (inTopContext . prettyTCM =<< getContextTelescope)
          , "tel   =" <+> (inTopContext . prettyTCM $ tel)
          ]
        ]
      -- Andreas, 2021-05-11, issue #5378
      -- The impossible is sometimes possible, so splitting out this part...
      reportSDoc "tc.rec.proj" 5 $ nest 2 $ vcat
          [ "ftel1 =" <+> escapeContext impossible 1 (prettyTCM ftel1)
          , "t     =" <+> escapeContext impossible 1 (addContext ftel1 $ prettyTCM t)
          , "ftel2 =" <+> escapeContext impossible 1 (addContext ftel1 $ underAbstraction dom ftel2 prettyTCM)
          ]
      reportSDoc "tc.rec.proj" 55 $ nest 2 $ vcat
          [ "ftel1 (raw) =" <+> pretty ftel1
          , "t     (raw) =" <+> pretty t
          , "ftel2 (raw) =" <+> pretty ftel2
          ]
      reportSDoc "tc.rec.proj" 5 $ nest 2 $ vcat
          [ "vs    =" <+> prettyList_ (map prettyTCM vs)
          , "abstr =" <+> (text . show) (Info.defAbstract info)
          , "quant =" <+> (text . show) (getQuantity ai)
          , "coh   =" <+> (text . show) (getCohesion ai)
          ]

      -- Cohesion check:
      -- For a field `@c π : A` we would create a projection `π : .., (@(c^-1) r : R as) -> A`
      -- So we want to check that `@.., (c^-1 . c) x : A |- x : A` is allowed by the modalities.
      --
      -- Alternatively we could create a projection `.. |- π r :c A`
      -- but that would require support for a `t :c A` judgment.
      if hasLeftAdjoint (UnderComposition (getCohesion ai))
        then unless (getCohesion ai == Continuous)
                    -- Andrea TODO: properly update the context/type of the projection when we add Sharp
                    __IMPOSSIBLE__
        else genericError $ "Cannot have record fields with modality " ++ show (getCohesion ai)

      -- The telescope tel includes the variable of record type as last one
      -- e.g. for cartesion product it is
      --
      --   tel = {A' : Set} {B' : Set} (r : Prod A' B')

      -- create the projection functions (instantiate the type with the values
      -- of the previous fields)

      -- The type of the projection function should be
      --  {Δ} -> (r : R Δ) -> t
      -- where Δ are the parameters of R

      {- what are the contexts?

          Δ , ftel₁              ⊢ t
          Δ , (r : R Δ)          ⊢ parallelS vs : ftel₁
          Δ , (r : R Δ) , ftel₁  ⊢ t' = raiseFrom (size ftel₁) 1 t
          Δ , (r : R Δ)          ⊢ t'' = applySubst (parallelS vs) t'
                                 ⊢ finalt = telePi tel t''
      -}
      let t'       = raiseFrom (size ftel1) 1 t
          t''      = applySubst (parallelS vs) t'
          finalt   = telePi (replaceEmptyName "r" tel) t''
          projname = qualify m $ qnameName x
          projcall o = Var 0 [Proj o projname]
          rel      = getRelevance ai
          -- the recursive call
          recurse  = checkProjs (abstract ftel1 $ ExtendTel dom
                                 $ Abs (nameToArgName $ qnameName projname) EmptyTel)
                                (absBody ftel2) (projcall ProjSystem : vs) fs

      reportSDoc "tc.rec.proj" 25 $ nest 2 $ "finalt=" <+> do
        inTopContext $ prettyTCM finalt

      -- -- Andreas, 2012-02-20 do not add irrelevant projections if
      -- -- disabled by --no-irrelevant-projections
      -- ifM (return (rel == Irrelevant) `and2M` do not . optIrrelevantProjections <$> pragmaOptions) recurse $ do
      -- Andreas, 2018-06-09 issue #2170
      -- Always create irrelevant projections (because the scope checker accepts irrelevant fields).
      -- If --no-irrelevant-projections, then their use should be disallowed by the type checker for expressions.
      do
        reportSDoc "tc.rec.proj" 10 $ sep
          [ "adding projection"
          , nest 2 $ prettyTCM projname <+> ":" <+> inTopContext (prettyTCM finalt)
          ]

        -- The body should be
        --  P.xi {tel} (r _ .. x .. _) = x
        -- Ulf, 2011-08-22: actually we're dropping the parameters from the
        -- projection functions so the body is now
        --  P.xi (r _ .. x .. _) = x
        -- Andreas, 2012-01-12: irrelevant projections get translated to
        --  P.xi (r _ .. x .. _) = irrAxiom {level of t} {t} x
        -- PROBLEM: because of dropped parameters, cannot refer to t
        -- 2012-04-02: DontCare instead of irrAxiom

        -- compute body modification for irrelevant projections
        let bodyMod = case rel of
              Relevant   -> id
              NonStrict  -> id
              Irrelevant -> dontCare

        let -- Andreas, 2010-09-09: comment for existing code
            -- split the telescope into parameters (ptel) and the type or the record
            -- (rt) which should be  R ptel
            telList = telToList tel
            (ptelList,[rt]) = splitAt (size tel - 1) telList
            ptel   = telFromList ptelList
            cpo    = if hasNamedCon then PatOCon else PatORec
            cpi    = ConPatternInfo { conPInfo   = PatternInfo cpo []
                                    , conPRecord = True
                                    , conPFallThrough = False
                                    , conPType   = Just $ argFromDom $ fmap snd rt
                                    , conPLazy   = True }
            conp   = defaultNamedArg $ ConP con cpi $ teleNamedArgs ftel
            body   = Just $ bodyMod $ var (size ftel2)
            cltel  = ptel `abstract` ftel
            cltype = Just $ Arg ai $ raise (1 + size ftel2) t
            clause = Clause { clauseLHSRange  = getRange info
                            , clauseFullRange = getRange info
                            , clauseTel       = killRange cltel
                            , namedClausePats = [conp]
                            , clauseBody      = body
                            , clauseType      = cltype
                            , clauseCatchall  = False
                            , clauseExact       = Just True
                            , clauseRecursive   = Just False
                            , clauseUnreachable = Just False
                            , clauseEllipsis    = NoEllipsis
                            , clauseWhereModule = Nothing
                            }

        let projection = Projection
              { projProper   = Just r
              , projOrig     = projname
              -- name of the record type:
              , projFromType = defaultArg r
              -- index of the record argument (in the type),
              -- start counting with 1:
              , projIndex    = size tel -- which is @size ptel + 1@
              , projLams     = ProjLams $ map (argFromDom . fmap fst) telList
              }

        reportSDoc "tc.rec.proj" 70 $ sep
          [ "adding projection"
          , nest 2 $ prettyTCM projname <+> pretty clause
          ]
        reportSDoc "tc.rec.proj" 10 $ sep
          [ "adding projection"
          , nest 2 $ prettyTCM (QNamed projname clause)
          ]

              -- Record patterns should /not/ be translated when the
              -- projection functions are defined. Record pattern
              -- translation is defined in terms of projection
              -- functions.
        (mst, _, cc) <- compileClauses Nothing [clause]

        reportSDoc "tc.cc" 60 $ do
          sep [ "compiled clauses of " <+> prettyTCM projname
              , nest 2 $ text (show cc)
              ]

        escapeContext impossible (size tel) $ do
          lang <- getLanguage
          fun  <- emptyFunctionData
          let -- It should be fine to mark a field with @ω in an
              -- erased record type: the field will be non-erased, but
              -- the projection will be erased. The following code
              -- ensures that the use of addConstant does not trigger
              -- a PlentyInHardCompileTimeMode warning.
              ai' = flip mapQuantity ai $ \case
                      Quantityω _ -> Quantityω QωInferred
                      q           -> q
          addConstant projname $
            (defaultDefn ai' projname (killRange finalt) lang $ FunctionDefn
              fun
                { _funClauses        = [clause]
                , _funCompiled       = Just cc
                , _funSplitTree      = mst
                , _funProjection     = Right projection
                , _funMutual         = Just []  -- Projections are not mutually recursive with anything
                , _funTerminates     = Just True
                })
              { defArgOccurrences = [StrictPos]
              , defCopatternLHS   = hasProjectionPatterns cc
              }
          computePolarity [projname]

        case Info.defInstance info of
          -- fields do not have an @instance@ keyword!?
          InstanceDef _r -> addTypedInstance projname t
          NotInstanceDef -> pure ()

        recurse

    -- Case: definition.
    checkProjs ftel1 ftel2 vs (d : fs) = do
      checkProjs ftel1 ftel2 vs fs
