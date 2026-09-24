{-# LANGUAGE LinearTypes, ScopedTypeVariables, TypeApplications, TypeFamilies #-}
module MissingDictionary where
import Linear.Logic
bad :: forall a r. Not a %1 -> a %1 -> r
bad = (!=) @(Not a)
