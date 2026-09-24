{-# LANGUAGE GADTs, TypeFamilies, TypeOperators #-}
module ForeignNot where
import Data.Type.Equality
import Linear.Logic ()
type family Not a
bad :: Not (Not a) :~: a
bad = Refl
