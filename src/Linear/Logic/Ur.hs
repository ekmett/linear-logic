{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Trustworthy #-}
{-# options_ghc -Wno-orphans #-}

module Linear.Logic.Ur 
  ( Ur(..)
  ) where

import Data.Unrestricted.Linear

deriving stock instance Show a => Show (Ur a)
deriving stock instance Read a => Read (Ur a)
deriving stock instance Eq a => Eq (Ur a)
deriving stock instance Ord a => Ord (Ur a)
