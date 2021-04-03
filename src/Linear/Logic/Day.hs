
{-# language LinearTypes #-}
{-# language RankNTypes #-}
{-# language LambdaCase #-}
{-# language EmptyCase #-}
{-# language ScopedTypeVariables #-}
{-# language Trustworthy #-}
{-# language BlockArguments #-}
{-# language TypeOperators #-}
{-# language ConstraintKinds #-}
{-# language GADTs #-}
{-# language NoImplicitPrelude #-}
{-# language TypeFamilies #-}
{-# language TypeApplications #-}
{-# options_ghc -Wno-unused-imports -fplugin Linear.Logic.Plugin #-}

module Linear.Logic.Day where

import Data.Kind
import Data.Unrestricted.Linear (Ur(..))
import GHC.Types
import Linear.Logic.Internal
import Linear.Logic.Functor
import Linear.Logic.Y
import Prelude.Linear ((&))

-- | Day convolution of logical functors
data Day f g a where
  Day :: (Prop b, Prop c) => ((b,c) ⊸ a) %1 -> f b %1 -> g c %1 -> Day f g a

-- | refuted Day convolution of logical functors
newtype Noday f g a = Noday 
  ( forall b c. (Prop b, Prop c) =>
    (a <#- (b,c)) ⅋ Not (f b) ⅋ Not (g c)
  )

instance (Functor f, Functor g, Prop a) => Prop (Day f g a) where
  type Not (Day f g a) = Noday f g a 
  Day bca (fb :: f b) gc != Noday no = (bca,(fb,gc)) != no

instance (Functor f, Functor g, Prop a) => Prop (Noday f g a) where
  type Not (Noday f g a) = Day f g a
  Noday no != Day bca (fb :: f b) gc = (bca,(fb,gc)) != no
