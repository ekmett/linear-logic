{-# LANGUAGE GADTs, TypeFamilies, TypeOperators #-}
module WrongReverseEquality where
import Data.Type.Equality
import Linear.Logic
bad :: Bool :~: Not (Not Int)
bad = Refl
