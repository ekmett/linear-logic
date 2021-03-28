{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# options_ghc -Wno-orphans #-}

module Linear.Logic.Orphans () where

import Data.Unrestricted.Linear

deriving stock instance Show a => Show (Ur a)
deriving stock instance Read a => Read (Ur a)
deriving stock instance Eq a => Eq (Ur a)
deriving stock instance Ord a => Ord (Ur a)
