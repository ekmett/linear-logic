{-# language BlockArguments #-}
{-# language CPP #-}
{-# language LambdaCase #-}
{-# language Trustworthy #-}
{-# language RecordWildCards #-}
{-# options_ghc -Wno-unused-matches #-}

-- | GHC typechecker plugin for simplifying 'Not' constraints.
--
-- Usage:
--
-- @
-- {-# OPTIONS_GHC -fplugin Linear.Logic.Plugin #-}
-- @
--
-- This plugin proves equalities of the form @Not (Not a) ~ a@ by
-- turning them into plain type equalities. It is intended to reduce
-- the amount of manual 'Prep' evidence required when working with
-- double-negation.
module Linear.Logic.Plugin where

-- import Control.Monad
import Control.Monad.IO.Class
-- import Data.Foldable (traverse_)
import GHC.Builtin.Names
import GHC.Builtin.Types
-- import GHC.Core
-- import GHC.Core.Coercion
import GHC.Core.Coercion (mkPrimEqPred)
import GHC.Core.Predicate (EqRel(..), Pred(..), classifyPredType)
import GHC.Core.Type
-- import GHC.Core.TyCo.Rep
import GHC.Driver.Plugins (Plugin(..), defaultPlugin, purePlugin)
-- import GHC.Driver.Session
import GHC.Types.Name.Occurrence
import GHC.Types.Unique.FM (emptyUFM)
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.TcPluginM.Extra (tracePlugin, evByFiat)
-- import GHC.Types.Var
#if __GLASGOW_HASKELL__ >= 908
import GHC.Unit.Module (mkModuleName)
#else
import GHC.Unit.Module.Name (mkModuleName)
#endif
-- import GHC.Unit.Types
import GHC.Types.PkgQual (PkgQual(..))
import GHC.Utils.Outputable

-- Not (Not a) ~ b   ==> a ~ b

-- TODO: want (Prop a) and have Prop (Not a) -- give me Prop (Not (Not a))

plugin :: Plugin
plugin = defaultPlugin
  { tcPlugin = \_ -> Just logicPlugin
  , pluginRecompile = purePlugin
  } where

logicPlugin :: TcPlugin
logicPlugin = tracePlugin "linear-logic"
  TcPlugin
  { tcPluginInit = tcPluginIO $ pure ()
  , tcPluginSolve = solveLogic
  , tcPluginRewrite = const emptyUFM
  , tcPluginStop = const $ pure ()
  }

io :: IO a -> TcPluginM a
io = unsafeTcPluginTcM . liftIO

pp :: Outputable a => a -> String
pp = showSDocUnsafe . ppr

-- TODO: this is going to require me to rummage through givens for parts

solveLogic :: () -> TcPluginSolver
#if __GLASGOW_HASKELL__ >= 904
solveLogic () _evb givens wanteds = do
#else
solveLogic () _evb givens _deriveds wanteds = do
#endif
  Found _ lli <- findImportedModule (mkModuleName "Linear.Logic.Internal") NoPkgQual
  notName <- lookupOrig lli (mkTcOcc "Not")
  notTyCon <- tcLookupTyCon notName
  let notKey = getUnique notTyCon


{-
  unless (null wanteds) $ io do
    putStrLn "solveLogic\n"
    putStrLn "  wanteds:"
    traverse_ (\x -> putStrLn $ "    " ++ pp (ctLocSpan (ctLoc x)) ++ " " ++ pp x) wanteds
    putStrLn "  givens:"
    traverse_ (\x -> putStrLn $ "    " ++ pp (ctLocSpan (ctLoc x)) ++ " " ++ pp x) givens
    putStrLn "\n\n"
-}

  let

{-
    is :: Type -> Type -> Bool
    is (TyVarTy x) (TyVarTy x') = varUnique x == varUnique x'
   -- is _ _ = False

    isNot :: Type -> Type -> Ct -> Bool
    isNot y x g = case classifyPredType $ ctEvPred $ ctEvidence g of
      EqPred NomEq ny' x'
        | Just (n1, [y']) <- splitTyConApp_maybe ny', hasKey n1 notKey
        -> is y y' && is x x'
      _ -> False

    findNot :: Type -> Type -> [Ct] -> Bool
    findNot y x = any (isNot y x) 
-}

    runEvExpr (EvExpr x) = x
    runEvExpr _ = error "runEvExpr"

    tryToSolve :: Ct -> TcPluginM ([(EvTerm,Ct)],[Ct])
    tryToSolve ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq nnx y
        | Just (n1, [nx]) <- splitTyConApp_maybe nnx, hasKey n1 notKey
        , Just (n2, [x]) <- splitTyConApp_maybe nx, hasKey n2 notKey
        -> do
          wantedEvidence <- newWanted (ctLoc ct) (mkPrimEqPred x y)
          -- io $ putStrLn $ "not-not: " ++ pp nnx ++ " ~ " ++ pp y ++ " if " ++ pp x ++ " ~ " ++ pp y
          pure ([(evByFiat "not-not" nnx y, ct)],[mkNonCanonical wantedEvidence])
      EqPred NomEq y nnx
        | Just (n1, [nx]) <- splitTyConApp_maybe nnx, hasKey n1 notKey
        , Just (n2, [x]) <- splitTyConApp_maybe nx, hasKey n2 notKey
        -> do
          wantedEvidence <- newWanted (ctLoc ct) (mkPrimEqPred x y)
          -- io $ putStrLn $ "not-not: " ++ pp y ++ " ~ " ++ pp nnx ++ " if " ++ pp x ++ " ~ " ++ pp y
          pure ([(evByFiat "not-not" nnx y, ct)],[mkNonCanonical wantedEvidence])
      EqPred NomEq nx y
        | Just (n1, [_x]) <- splitTyConApp_maybe nx, hasKey n1 notKey
        -> pure ([], [])
      EqPred n x y -> do
       -- io $ putStrLn $ "I think " ++ pp n ++ " " ++ pp x ++ pp y ++ " is none of my business"
        pure ([],[])
      ClassPred c [_star, nnx, y]
        | hasKey c eqTyConKey 
        , Just (n1, [nx]) <- splitTyConApp_maybe nnx, hasKey n1 notKey
        , Just (n2, [x]) <- splitTyConApp_maybe nx, hasKey n2 notKey
        -> do
        -- io $ putStrLn $ "Ooh ooh ooh: " ++ show (pp c, pp x, pp y)
        wantedEvidence <- newWanted (ctLoc ct) (mkPrimEqPred x y)


        pure ([(evDataConApp eqDataCon [liftedTypeKind,x,y] [runEvExpr $ evByFiat "not-not" x y], ct)],[mkNonCanonical wantedEvidence])
      ClassPred c tys -> do
        -- io $ putStrLn $ "ClassPred " ++ show (pp c, pp tys)
        pure ([],[])
      IrredPred ty -> do
        -- io $ putStrLn $ "IrredPred " ++ pp ty
        pure ([],[])
      ForAllPred as bs cs -> do
        -- io $ putStrLn $ "ForAllPred " ++ show (pp as, pp bs, pp cs)
        pure ([],[])

  results <- traverse tryToSolve wanteds
  pure $ TcPluginOk (results >>= fst) (results >>= snd)
