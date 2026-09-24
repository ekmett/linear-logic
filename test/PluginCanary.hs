{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Data.Type.Equality (type (~))
import Linear.Logic.Internal (Not)
import Prelude (IO, Int, putStrLn)

type Canary = Not (Not Int) ~ Int

canary :: Canary => ()
canary = ()

main :: IO ()
main = do
  let _ = canary
  putStrLn "plugin ok"
