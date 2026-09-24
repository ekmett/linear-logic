{-# LANGUAGE GADTs, LinearTypes, ScopedTypeVariables, TypeApplications, TypeFamilies #-}
module ScopedDictionary where

import Linear.Logic

data Witness a where
  Present :: Prop a => Witness a
  Absent :: Witness a

-- Evidence obtained in the first branch must not escape to its sibling.
bad :: forall a r. Witness a -> Not a %1 -> a %1 -> r
bad Present = (!=) @(Not a)
bad Absent = (!=) @(Not a)
