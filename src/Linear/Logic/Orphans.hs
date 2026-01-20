{-# language CPP #-}
{-# language NoImplicitPrelude #-}
{-# language StandaloneDeriving #-}
{-# language DerivingStrategies #-}
{-# language ImportQualifiedPost #-}
{-# language LambdaCase #-}
{-# language EmptyCase #-}
{-# language Trustworthy #-}
{-# options_ghc -Wno-orphans #-}

module Linear.Logic.Orphans where

import Control.Category as C
import Data.Kind
#if !MIN_VERSION_linear_base(0,2,0)
import Data.Void
#endif
import Prelude.Linear
import Prelude qualified

instance {-# OVERLAPPABLE #-} C.Category (FUN m) where
  id x = x
  f . g = \x -> f (g x)

deriving stock instance Show a => Show (Ur a)
deriving stock instance Read a => Read (Ur a)
deriving stock instance Prelude.Eq a => Prelude.Eq (Ur a)
deriving stock instance Prelude.Ord a => Prelude.Ord (Ur a)

#if !MIN_VERSION_linear_base(0,2,0)
instance Consumable Void where
  consume = \case

instance Dupable Void where
  dup2 = \case
#endif
