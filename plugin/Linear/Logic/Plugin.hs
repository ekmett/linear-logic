{-# language CPP #-}
{-# language NamedFieldPuns #-}
{-# language Trustworthy #-}

-- | Opt-in laws for linear logic:
--
-- * @Not (Not a) ~ a@, including occurrences inside other types.
-- * @Prop a => Prop (Not a)@, exchanging the given dictionary's
--   @(!=)@ and @(=!)@ method fields with erased type coercions.
--
-- Enable with @-fplugin Linear.Logic.Plugin@ in client modules. The
-- involution is an axiom of this embedding; the plugin never asserts
-- arbitrary equalities and never invents a proposition dictionary without
-- an existing dictionary for its dual.
module Linear.Logic.Plugin (plugin) where

import Control.Monad (foldM)
import Data.Maybe (listToMaybe)
import GHC.Builtin.Types (oneDataConTy)
import GHC.Core (Expr(..), CoreExpr)
import GHC.Core.Class (Class, classMethods, classTyCon, classSCTheta)
import GHC.Core.Coercion
import GHC.Core.Make (mkCoreApps)
import GHC.Core.Predicate (EqRel(..), Pred(..), classifyPredType, mkClassPred)
#if __GLASGOW_HASKELL__ >= 914
import GHC.Core.Predicate (mkNomEqPred)
#endif
import GHC.Core.Reduction (Reduction(..))
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
#if __GLASGOW_HASKELL__ >= 910
import GHC.Core.TyCo.Compare (eqType)
#endif
import GHC.Core.TyCon (TyCon, isTypeFamilyTyCon)
import GHC.Core.Type
import GHC.Data.FastString (fsLit)
import GHC.Driver.Plugins (Plugin(..), defaultPlugin, purePlugin)
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.TcType (isMetaTyVar)
import GHC.Types.Id (Id)
import GHC.Types.Name (mkSysTvName)
import GHC.Types.Name.Occurrence (mkTcOcc)
import GHC.Types.PkgQual (PkgQual(..))
import GHC.Types.Unique.FM (unitUFM)
import GHC.Types.Var (mkTyVar)
import GHC.Types.Var.Set (elemVarSet)
#if __GLASGOW_HASKELL__ >= 908
import GHC.Unit.Module (mkModuleName)
#else
import GHC.Unit.Module.Name (mkModuleName)
#endif
#if __GLASGOW_HASKELL__ < 914
import GHC.Core.TyCon (tyConSingleDataCon)
#endif

-- Resolve names once, and compare actual TyCons rather than printed names.
data Logic = Logic
  { notCon :: TyCon
  , propClass :: Class
  , refuteId :: Id
  , flippedId :: Id
  }

plugin :: Plugin
plugin = defaultPlugin
  { tcPlugin = const (Just logicPlugin)
  , pluginRecompile = purePlugin
  }

logicPlugin :: TcPlugin
logicPlugin = TcPlugin
  { tcPluginInit = initialise
  , tcPluginSolve = solve
  , tcPluginRewrite = \logic -> unitUFM (notCon logic) (rewriteNot logic)
  , tcPluginStop = const (pure ())
  }

initialise :: TcPluginM Logic
initialise = do
  found <- findImportedModule (mkModuleName "Linear.Logic.Prop") NoPkgQual
  mdl <- case found of
    Found _ mdl -> pure mdl
    _ -> fail "Linear.Logic.Plugin: cannot find Linear.Logic.Prop"
  notCon <- lookupOrig mdl (mkTcOcc "Not") >>= tcLookupTyCon
  propClass <- lookupOrig mdl (mkTcOcc "Prop") >>= tcLookupClass
  case classMethods propClass of
    [refuteId, flippedId] | null (classSCTheta propClass) ->
      pure Logic{notCon, propClass, refuteId, flippedId}
    _ -> fail "Linear.Logic.Plugin: expected Prop to have two refutation methods and no superclasses"

notType :: Logic -> Type -> Type
notType Logic{notCon} a = mkTyConApp notCon [a]

splitNot :: Logic -> Type -> Maybe Type
splitNot Logic{notCon} ty = case splitTyConApp_maybe ty of
  Just (tc, [a]) | tc == notCon -> Just a
  _ -> Nothing

-- This is the sole plugin axiom. All other coercions are composed from it
-- and GHC's own evidence. No local givens are needed to justify this law.
involution :: Logic -> Type -> Coercion
involution logic a =
#if __GLASGOW_HASKELL__ >= 912
  mkUnivCo (PluginProv "linear-logic: involution") [] Nominal
#else
  mkUnivCo (PluginProv "linear-logic: involution") Nominal
#endif
    (notType logic (notType logic a)) a

rewriteNot :: Logic -> TcPluginRewriter
rewriteNot logic _env givens [na] = pure $ case notReduction logic givens na of
  Just reduction -> TcPluginRewriteTo reduction []
  Nothing -> TcPluginNoRewrite
rewriteNot _ _ _ _ = pure TcPluginNoRewrite

notReduction :: Logic -> [Ct] -> Type -> Maybe Reduction
notReduction logic givens na
  | Just a <- splitNot logic na =
      Just (Reduction (involution logic a) a)
  | Just (a, co) <- listToMaybe
      [ (a, co)
      | ct <- givens
      , EqPred NomEq lhs rhs <- [classifyPredType (ctPred ct)]
      , (other, same, co) <-
          [(lhs, rhs, mkSymCo (ctEvCoercion (ctEvidence ct))),
           (rhs, lhs, ctEvCoercion (ctEvidence ct))]
      , eqType same na
      , Just a <- [splitNot logic other]
      ] =
      -- If a given says Not a ~ b, Not b reduces to a even though the
      -- inner Not has already been replaced by b. Retain that given's
      -- coercion explicitly so the proof cannot escape its implication.
      Just (Reduction
        (mkTransCo (mkTyConAppCo Nominal (notCon logic) [co])
          (involution logic a)) a)
  | otherwise = Nothing

solve :: Logic -> TcPluginSolver
solve logic@Logic{propClass} evBinds givens wanteds
  | null wanteds = do
      -- Supply dual givens before GHC commits to a global instance for a
      -- compound dual. Work only in this implication's evidence environment.
      known <- traverse (normalForm logic givens . fst) sources
      equations <- traverse (\(a,b) -> (,) <$> normalForm logic givens a <*> normalForm logic givens b)
        [(a,b) | ct <- givens, EqPred NomEq a b <- [classifyPredType (ctPred ct)]]
      (_, new) <- foldM (extend equations) (known, []) sourceConstraints
      pure (TcPluginOk [] new)
  | otherwise = do
      solved <- traverse solveWanted wanteds
      pure (TcPluginOk (concatMap fst solved) (concatMap snd solved))
  where
    sourceConstraints =
      [ (a, ct)
      | ct <- givens
      , ClassPred cls [a] <- [classifyPredType (ctPred ct)]
      , cls == propClass
      ]
    sources =
      [(a, ctEvExpr (ctEvidence ct)) | (a, ct) <- sourceConstraints]

    extend equations (known, new) (a, ct) = do
      target <- normalForm logic givens (notType logic a)
      if any (equivalent equations target) known
        then pure (known, new)
        else do
          evidence <- dualDictionary logic a (ctEvExpr (ctEvidence ct))
          given <- newGiven evBinds (ctLoc ct)
            (mkClassPred propClass [notType logic a]) evidence
          pure (target : known, mkNonCanonical given : new)

    solveWanted ct = case classifyPredType (ctPred ct) of
      ClassPred cls [target] | cls == propClass ->
        case listToMaybe
          [ (a, dict, co)
          | (a, dict) <- sources
          , let (dual, co) = case splitNot logic a of
                  Just b -> (b, involution logic b)
                  Nothing -> (notType logic a, mkNomReflCo (notType logic a))
          , eqType dual target
          ] of
          Just (a, dict, co) -> do
            evidence <- dualDictionary logic a dict
            let dictCo = mkTyConAppCo Representational (classTyCon propClass) [co]
            pure ([(EvExpr (Cast evidence dictCo), ct)], [])
          Nothing -> pure ([], [])
      EqPred NomEq lhs rhs
        | Just a <- splitNot logic lhs
        , invertible a rhs -> invert ct False a rhs
        | Just a <- splitNot logic rhs
        , invertible a lhs -> invert ct True a lhs
      _ -> pure ([], [])

    invertible a b = case getTyVar_maybe a of
      Just v -> isMetaTyVar v && not (v `elemVarSet` tyCoVarsOfType b)
      Nothing -> False

    -- Not is injective AND surjective. GHC knows the former from its family
    -- declaration; expose the latter only for a metavariable, so this strictly
    -- advances inference rather than oscillating between equivalent equations.
    -- Crucially, the solved evidence depends on the new wanted coercion.
    invert ct reversed a b = do
      wanted <- newWanted (ctLoc ct) (mkNomEqPred a (notType logic b))
      let co = mkTransCo
            (mkTyConAppCo Nominal (notCon logic) [ctEvCoercion wanted])
            (involution logic b)
      pure ([(evCoercion (if reversed then mkSymCo co else co), ct)],
            [mkNonCanonical wanted])

#if __GLASGOW_HASKELL__ < 914
mkNomEqPred :: Type -> Type -> PredType
mkNomEqPred = mkPrimEqPred
#endif

-- Canonical keys for duplicate detection only. Actual evidence is always
-- constructed at the original types and rewritten by GHC. Expanding ordinary
-- family equations as well as involution prevents an endless stream of duals
-- when Not (Either a b), for example, reduces to Not a & Not b.
normalForm :: Logic -> [Ct] -> Type -> TcPluginM Type
normalForm logic givens = go (64 :: Int)
  where
    go 0 ty = pure ty
    go fuel ty = case splitTyConApp_maybe ty of
      Just (tc, args) -> do
        args' <- traverse (go (fuel - 1)) args
        let ty' = mkTyConApp tc args'
        case splitNot logic ty' >>= notReduction logic givens of
          Just (Reduction _ a) -> go (fuel - 1) a
          Nothing | isTypeFamilyTyCon tc -> do
            reduced <- matchFam tc args'
            case reduced of
              Just (Reduction _ rhs) -> go (fuel - 1) rhs
              Nothing -> pure ty'
          Nothing -> pure ty'
      Nothing -> case splitAppTy_maybe ty of
        Just (f, a) -> mkAppTy <$> go (fuel - 1) f <*> go (fuel - 1) a
        Nothing -> pure ty

-- Equality givens can identify a normalised dual with an existing dictionary.
-- This is used only to avoid producing redundant givens, never to forge a cast.
equivalent :: [(Type, Type)] -> Type -> Type -> Bool
equivalent equations start target = search [] [start]
  where
    search _ [] = False
    search seen (x:xs)
      | eqType x target = True
      | any (eqType x) seen = search seen xs
      | otherwise = search (x:seen)
          ([b | (a,b) <- equations, eqType x a] ++
           [a | (a,b) <- equations, eqType x b] ++ xs)

-- Swap the two existing polymorphic method fields, using erased casts to
-- transport their argument types along involution. There are no new term
-- lambdas: repeated dualization does not accumulate runtime flip wrappers.
dualDictionary :: Logic -> Type -> CoreExpr -> TcPluginM CoreExpr
dualDictionary logic@Logic{propClass, refuteId, flippedId} a dict = do
  resultUnique <- newUnique
  xUnique <- newUnique
  yUnique <- newUnique
  let na = notType logic a
      result = mkTyVar (mkSysTvName resultUnique (fsLit "r")) liftedTypeKind
      x = mkTyVar (mkSysTvName xUnique (fsLit "x")) liftedTypeKind
      y = mkTyVar (mkSysTvName yUnique (fsLit "y")) liftedTypeKind
      methodType = mkSpecForAllTy result $
        mkVisFunTy oneDataConTy (mkTyVarTy x) $
        mkVisFunTy oneDataConTy (mkTyVarTy y) (mkTyVarTy result)
      same = mkNomReflCo na
      nn = mkSymCo (involution logic a)
      slot method coercions = Cast (mkCoreApps (Var method) [Type a, dict])
        (liftCoSubstWith Representational [x,y] coercions methodType)
      forward = slot flippedId [same, nn]
      backward = slot refuteId [nn, same]
  pure (dictionary propClass [na] [forward, backward])

dictionary :: Class -> [Type] -> [CoreExpr] -> CoreExpr
#if __GLASGOW_HASKELL__ >= 914
dictionary cls tys args = case evDictApp cls tys args of
#else
dictionary cls tys args = case evDataConApp (tyConSingleDataCon (classTyCon cls)) tys args of
#endif
  EvExpr expr -> expr
  _ -> error "Linear.Logic.Plugin: dictionary evidence is not an expression"
