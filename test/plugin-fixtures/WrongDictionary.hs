{-# LANGUAGE LinearTypes, ScopedTypeVariables, TypeApplications, TypeFamilies #-}
module WrongDictionary where
import Linear.Logic
bad :: forall a b r. Prop a => Not b %1 -> b %1 -> r
bad = (!=) @(Not b)
