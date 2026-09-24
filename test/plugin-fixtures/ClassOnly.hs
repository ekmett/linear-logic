{-# LANGUAGE GADTs, LinearTypes, ScopedTypeVariables, TypeApplications, TypeFamilies, TypeOperators #-}
module ClassOnly where

import Data.Type.Equality
import Linear.Logic.Prop

involution :: Not (Not a) :~: a
involution = Refl

dual :: forall a r. Prop a => Not a %1 -> a %1 -> r
dual = (!=) @(Not a)
