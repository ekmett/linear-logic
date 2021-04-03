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

module Linear.Logic.Yoneda
( Yoneda(..)
, Noneda(..)
, liftYoneda
, lowerYoneda'
, lowerYoneda
, Coyoneda(..)
, Cononeda(..), cononeda, runCononeda
, liftCoyoneda'
, liftCoyoneda
, lowerCoyoneda
) where

import Data.Kind
import GHC.Types
import Data.Unrestricted.Linear (Ur(..))
import Linear.Logic.Internal
import Linear.Logic.Functor
import Linear.Logic.Y

newtype Yoneda f a = Yoneda (forall r. Prop r => Ur (a ⊸ r) ⊸ f r)

data Noneda f a where
  Noneda :: Prop r => {-# unpack #-} !(f r <#- Ur (a ⊸ r)) %1 -> Noneda f a

instance (Functor f, Prop a) => Prop (Yoneda f a) where
  type Not (Yoneda f a) = Noneda f a
  Yoneda y != Noneda n = y != n

instance (Functor f, Prop a) => Prop (Noneda f a) where
  type Not (Noneda f a) = Yoneda f a
  Noneda y != Yoneda n = y != n

runYoneda :: Prop r => Yoneda f a %1 -> (a ⊸ r) -> f r
runYoneda (Yoneda f) a2r = fun' f (Ur a2r)

lowerYoneda' :: (Prop a, Lol l) => l (Yoneda f a) (f a)
lowerYoneda' = lol \case
  L -> \nfa -> Noneda (Ur id :-#> nfa)
  R -> \f -> runYoneda f id

liftYoneda :: forall f a i. (Functor f, Prop a, Iso i) => i (f a) (Yoneda f a)
liftYoneda = iso \case
  L -> lowerYoneda'
  R -> lol \case
    L -> \(Noneda (Ur (a2r :: a ⊸ r) :-#> nfr)) -> runLol (fmap @f @a @r a2r) L nfr
    R -> \fa -> Yoneda do
      lol \case
        R -> \f -> fmap' f fa
        L -> \nfr -> whyNot \a2r -> fmap a2r fa != nfr

lowerYoneda :: forall f a i. (Functor f, Prop a, Iso i) => i (Yoneda f a) (f a)
lowerYoneda = inv' liftYoneda

data Coyoneda f a where
  Coyoneda :: Prop r => (r ⊸ a) -> f r %1 -> Coyoneda f a

newtype Cononeda f a = Cononeda (forall r. Prop r => f r ⊸ WhyNot (a <#- r))

runCononeda :: forall r l a f. (Prop r, Lol l) => Cononeda f a %1 -> l (f r) (WhyNot (a <#- r))
runCononeda (Cononeda f) = fun f

instance (Functor f, Prop a) => Prop (Coyoneda f a) where
  type Not (Coyoneda f a) = Cononeda f a
  Coyoneda r2a fr != k = because (runCononeda k fr) r2a

instance (Functor f, Prop a) => Prop (Cononeda f a) where
  type Not (Cononeda f a) = Coyoneda f a
  k != Coyoneda r2a fr = because (runCononeda k fr) r2a

cononeda :: (forall r. Prop r => f r ⊸ WhyNot (a <#- r)) %1 -> Cononeda f a
cononeda = Cononeda

-- | avoids the Functor constraint
liftCoyoneda' :: forall a f l. (Prop a, Lol l) => l (f a) (Coyoneda f a)
liftCoyoneda' = lol \case
  L -> \k -> runLol (runCononeda @a @(⊸) k) L (Ur id)
  R -> Coyoneda id

liftCoyoneda :: forall f a i. (Functor f, Prop a, Iso i) => i (f a) (Coyoneda f a)
liftCoyoneda = iso \case
  L -> lol \case
    L -> \nfa -> cononeda do
      lol \case
        L -> \(Ur r2a) -> runLol (fmap r2a) L nfa
        R -> \fr -> whyNot \r2a -> fmap r2a fr != nfa
    R -> \(Coyoneda r2a fa) -> fmap r2a fa
  R -> liftCoyoneda'

lowerCoyoneda :: forall f a i. (Functor f, Prop a, Iso i) => i (Coyoneda f a) (f a)
lowerCoyoneda = inv' liftCoyoneda
