{-# LANGUAGE AllowAmbiguousTypes, GADTs, TypeFamilies, TypeOperators #-}
module OccursCheck where
import Data.Proxy
import Data.Type.Equality
import Linear.Logic
-- The plugin must not cycle between a ~ Not a and Not a ~ a.
loop :: a :~: Not a -> Proxy a
loop _ = Proxy
bad :: ()
bad = case loop Refl of Proxy -> ()
