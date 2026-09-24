{-# LANGUAGE GADTs, TypeFamilies, TypeOperators #-}
module WrongEquality where
import Data.Type.Equality
import Linear.Logic
bad :: Not (Not Int) :~: Bool
bad = Refl
