{-# language BlockArguments #-}
{-# language LambdaCase #-}
{-# language Trustworthy #-}
{-# language RecordWildCards #-}

module Linear.Logic.Plugin where

import Control.Monad.IO.Class
import Data.Foldable (traverse_)
import GHC.Builtin.Names
import GHC.Builtin.Types
import GHC.Builtin.Types.Prim
-- import GHC.Core
-- import GHC.Core.Coercion
import GHC.Core.Predicate
import GHC.Core.Type
-- import GHC.Core.TyCo.Rep
import GHC.Driver.Plugins (Plugin(..), defaultPlugin, purePlugin)
-- import GHC.Driver.Session
import GHC.Types.Name.Occurrence
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.TcPluginM.Extra (tracePlugin, evByFiat)
-- import GHC.Types.Unique
import GHC.Unit.Module.Name
-- import GHC.Unit.Types
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
  , tcPluginStop = const $ pure ()
  }

io :: IO a -> TcPluginM a
io = unsafeTcPluginTcM . liftIO 

pp :: Outputable a => a -> String
pp = showSDocUnsafe . ppr 

-- TODO: this is going to require me to rummage through givens for parts

solveLogic :: () -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
solveLogic () givens _deriveds wanteds = do
  Found _ lli <- findImportedModule (mkModuleName "Linear.Logic.Internal") Nothing
  notName <- lookupOrig lli (mkTcOcc "Not")
  notKey <- getUnique <$> tcLookupTyCon notName

{-
  io do 
    putStrLn "solveLogic\n"
    putStrLn "  wanteds:"
    traverse_ (\x -> putStrLn $ "    " ++ pp x) wanteds
    putStrLn "  givens:"
    traverse_ (\x -> putStrLn $ "    " ++ pp x) givens
    putStrLn "\n\n"
-}

  let 
    
    tryToSolve :: Ct -> TcPluginM ([(EvTerm,Ct)],[Ct])
    tryToSolve ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
      EqPred NomEq nnx y
        | Just (n1, [nx]) <- splitTyConApp_maybe nnx, hasKey n1 notKey
        , Just (n2, [x]) <- splitTyConApp_maybe nx, hasKey n2 notKey
        -> do
          wantedEvidence <- newWanted (ctLoc ct) $ mkTyConApp eqPrimTyCon [liftedTypeKind,liftedTypeKind,x,y]
          pure ([(evByFiat "not-not" nnx y, ct)],[mkNonCanonical wantedEvidence])
      EqPred NomEq y nnx
        | Just (n1, [nx]) <- splitTyConApp_maybe nnx, hasKey n1 notKey
        , Just (n2, [x]) <- splitTyConApp_maybe nx, hasKey n2 notKey
        -> do
          wantedEvidence <- newWanted (ctLoc ct) $ mkTyConApp eqPrimTyCon [liftedTypeKind,liftedTypeKind,x,y]
          pure ([(evByFiat "not-not" nnx y, ct)],[mkNonCanonical wantedEvidence])
      EqPred n x y -> do
        io $ putStrLn $ "EqPred " ++ show (pp n, pp x, pp y)
        pure ([],[])
      ClassPred c [ts] -> do
--        io $ putStrLn $ "ClassPred " ++ show (pp c, pp ts)
        pure ([],[])
      IrredPred ty -> do
--        io $ putStrLn $ "IrredPred " ++ show (pp ty)
        pure ([],[])
      ForAllPred tys ptys p -> do
--        io $ putStrLn $ "ForallPred " ++ show (pp tys, pp ptys, pp p)
        pure ([],[])
 
  results <- traverse tryToSolve wanteds
  pure $ TcPluginOk (results >>= fst) (results >>= snd)
