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
{-# options_ghc -Wno-unused-imports #-}

module Linear.Logic.Day where

import Data.Kind
import Data.Unrestricted.Linear (Ur(..))
import GHC.Types
import Linear.Logic.Internal
import Linear.Logic.Functor
import Linear.Logic.Y
import Prelude.Linear ((&))

data Dict p where
  Dict :: p => Dict p

newtype p :- q = Sub (p => Dict q)

propFunctor :: (Functor f, Prop a) :- Prop (f a)
propFunctor = Sub Dict

propPrep :: Prop a :- Prep a
propPrep = Sub Dict

(\\) :: p => (q => r) -> (p :- q) -> r
r \\ Sub Dict = r

compose :: (q :- r) -> (p :- q) -> p :- r
compose f g = Sub (Dict \\ f \\ g)

-- | Haskell is generally not willing to chase implications of quantified
-- constraints when you can't prove @Not (Not (f a) ~ f a@, but have @Functor f@ and
-- @Prop a@ in scope, this can be helpful.
--
prepFunctor :: forall f a. (Functor f, Prop a) :- Prep (f a)
prepFunctor = compose propPrep propFunctor

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
  Day bca (fb :: f b) gc != Noday no = case prepFunctor @f @b of
    Sub Dict -> (bca,(fb,gc)) != no

instance (Functor f, Functor g, Prop a) => Prop (Noday f g a) where
  type Not (Noday f g a) = Day f g a
  Noday no != Day bca (fb :: f b) gc = case prepFunctor @f @b of
    Sub Dict -> (bca,(fb,gc)) != no
