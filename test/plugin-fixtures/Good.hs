{-# LANGUAGE FlexibleContexts, GADTs, LinearTypes, ScopedTypeVariables, TypeApplications, TypeFamilies, TypeOperators #-}
module Good where
import Data.Type.Equality
import Data.Coerce (coerce)
import Linear.Logic

nested :: Either (Not (Not a)) (Not (Not b)) :~: Either a b
nested = Refl

flipped :: forall a r. Prop a => Not a %1 -> a %1 -> r
flipped = (!=) @(Not a)

representational :: Not (Not a) -> a
representational = coerce
