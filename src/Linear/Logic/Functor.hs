{-# language BlockArguments #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language ExplicitNamespaces #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language LinearTypes #-}
{-# language NoStarIsType #-}
{-# language PolyKinds #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language RoleAnnotations #-}
{-# language Safe #-}
{-# language StandaloneDeriving #-}
{-# language StandaloneKindSignatures #-}
{-# language StrictData #-}
{-# language TupleSections #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TypeFamilyDependencies #-}
{-# language TypeOperators #-}
{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}

module Linear.Logic.Functor
( Functor(..)
, Contravariant(..)
, Bifunctor(..)
, Semimonoidal(..)
, Monoidal(..)
, SymmetricMonoidal(..)
, swapPar
, swapEither
, swapWith
, swapTensor
, assocPar
, assocEither
, assocWith
, assocTensor
, unassocPar
, unassocEither
, unassocWith
, unassocTensor
) where

import Data.Void
import Data.Kind
import Linear.Logic
import Prelude hiding (Functor)

class
  ( forall a. Prop a => Prop (f a)
  ) => Functor f where
  fmap :: (Prop a, Prop b) => (a ⊸ b) -> f a ⊸ f b

instance Functor Ur where
  fmap f = par \case
    L -> \(No cb) -> No \a -> cb (fun f a)
    R -> \(Ur a) -> Ur (fun f a)
  {-# inline fmap #-}

instance Functor WhyNot where
  fmap f = par \case
    L -> \nb -> why (unfun f (runWhy nb))
    R -> \na2v -> whyNot \nb -> because na2v (unfun f nb)
  {-# inline fmap #-}

instance Prop a => Functor (Either a) where
  fmap f = par \case
    L -> \nawnb -> with \case
      L -> withL nawnb
      R -> unfun f (withR nawnb)
    R -> \case
      Left a -> Left a
      Right x -> Right (fun f x)

instance Prop x => Functor ((,) x) where
  fmap f = par \case
    L -> \nxpnb -> par \case
      L -> \a -> parL nxpnb (fun f a)
      R -> \x -> unfun f (parR nxpnb x)
    R -> \(x, a) -> (x, fun f a)
  {-# inline fmap #-}

instance Prop p => Functor ((&) p) where
  fmap f = par \case
    L -> \case
      Left np -> Left np
      Right nb -> Right (unfun f nb)
    R -> \pwa -> with \case
      L -> withL pwa
      R -> fun f (withR pwa)

instance Prop a => Functor ((⅋) a) where
  fmap f = par \case
    L -> \(na,nb) -> (na, unfun f nb)
    R -> \apa1 -> par \case
      L -> \nb -> parL apa1 (unfun f nb)
      R -> \na -> fun f (parR apa1 na)

class
  ( forall a. Prop a => Prop (f a)
  -- , forall a. Prop a => Functor (Not (f a))
  -- Not1 (Not1 f) ~ f
  ) => Contravariant f where
  contramap :: (Prop a, Prop b) => (a ⊸ b) -> f b ⊸ f a

instance Contravariant No where
  contramap f = par \case
    L -> \(Ur a) -> Ur (fun f a)
    R -> \(No cb) -> No \a -> cb (fun f a)
  {-# inline contramap #-}

instance Contravariant Why where
  contramap f = par \case
    L -> \na2v -> whyNot \nb -> because na2v (unfun f nb)
    R -> \nb -> why (unfun f (runWhy nb))

class
  ( forall a. Prop a => Functor (t a)
  ) => Bifunctor t where
  bimap
    :: (Prop a, Prop b, Prop c, Prop d)
    => (a ⊸ b)
    -> (c ⊸ d)
    -> t a c ⊸ t b d

instance Bifunctor Either where
  bimap f g = par \case
    L -> \nbwnd -> with \case
      L -> unfun f (withL nbwnd)
      R -> unfun g (withR nbwnd)
    R -> \case
      Left a -> Left (fun f a)
      Right c -> Right (fun g c)

instance Bifunctor (,) where
  bimap f g = par \case
    L -> \nbpnd -> par \case
      L -> \c -> unfun f (parL nbpnd (fun g c))
      R -> \a -> unfun g (parR nbpnd (fun f a))
    R -> \(a, c) -> (fun f a, fun g c)

instance Bifunctor (&) where
  bimap f g = par \case
    L -> \case
      Left nb  -> Left  (unfun f nb)
      Right nd -> Right (unfun g nd)
    R -> \awc -> with \case
      L -> fun f (withL awc)
      R -> fun g (withR awc)

instance Bifunctor (⅋) where
  bimap f g = par \case
    L -> \(nb,nd) -> (unfun f nb, unfun g nd)
    R -> \apc -> par \case
      L -> \nd -> fun f (parL apc (unfun g nd))
      R -> \nb -> fun g (parR apc (unfun f nb))

class Bifunctor t => Semimonoidal t where
  assoc :: (Prop a, Prop b, Prop c) => t (t a b) c ⊸ t a (t b c)
  unassoc :: (Prop a, Prop b, Prop c) => t a (t b c) ⊸ t (t a b) c

class (Prop (I t), Semimonoidal t) => Monoidal t where
  type I t :: Type
  lambda :: Prop a => a ⊸ t (I t) a
  unlambda :: Prop a => t (I t) a ⊸ a
  rho :: Prop a => a ⊸ t a (I t)
  unrho :: Prop a => t a (I t) ⊸ a

class Monoidal t => SymmetricMonoidal t where
  swap :: (Prop a, Prop b) => t a b ⊸ t b a

instance Semimonoidal Either where
  assoc = par \case
    L -> unassocWith
    R -> assocEither
  unassoc = swapPar assoc

instance Monoidal Either where
  type I Either = Void
  lambda = par \case
    L -> withR
    R -> Right
  unlambda = swapPar lambda
  rho = par \case
    L -> withL
    R -> Left
  unrho = swapPar rho

instance SymmetricMonoidal Either where
  swap = par \case
    L -> swapWith
    R -> swapEither

instance Semimonoidal (,) where
  assoc = par \case
    L -> unassocPar
    R -> assocTensor
  unassoc = swapPar assoc

instance Monoidal (,) where
  type I (,) = ()
  lambda = par \case
    L -> \bpa -> parR bpa ()
    R -> ((),)
  unlambda = swapPar lambda
  rho = par \case
    L -> \apb -> parL apb ()
    R -> (,())
  unrho = swapPar rho

instance SymmetricMonoidal (,) where
  swap = par \case
    L -> swapPar
    R -> swapTensor

instance Semimonoidal (&) where
  assoc = par \case
    L -> unassocEither
    R -> assocWith
  unassoc = swapPar assoc

instance Monoidal (&) where
  type I (&) = Top
  lambda = par \case
    L -> \case
      Right na -> na
      Left v -> \case{} v
    R -> \a -> with \case
      L -> Top a
      R -> a
  unlambda = swapPar lambda
  rho = par \case
    L -> \case
      Left na -> na
      Right v -> \case{} v
    R -> \b -> with \case
      L -> b
      R -> Top b
  unrho = swapPar rho

instance SymmetricMonoidal (&) where
  swap = par \case
    L -> swapEither
    R -> swapWith

instance Semimonoidal (⅋) where
  assoc = par \case
    L -> unassocTensor
    R -> assocPar
  unassoc = swapPar assoc

instance Monoidal (⅋) where
  type I (⅋) = Bot
  lambda = par \case
    L -> \((),na) -> na
    R -> \a -> par \case
      L -> \na -> a != na
      R -> \() -> a
  unlambda = swapPar lambda
  rho = par \case
    L -> \(na,()) -> na
    R -> \b -> par \case
      L -> \() -> b
      R -> \nb -> b != nb
  unrho = swapPar rho

instance SymmetricMonoidal (⅋) where
  swap = par \case
    L -> swapTensor
    R -> swapPar

swapPar :: p ⅋ q %1 -> q ⅋ p
swapPar = \apb -> par \case
  L -> \na -> parR apb na
  R -> \nb -> parL apb nb

swapEither :: p + q %1 -> q + p
swapEither = \case
  Left p -> Right p
  Right q -> Left q

swapWith :: p & q %1 -> q & p
swapWith w = with \case
  L -> withR w
  R -> withL w

swapTensor :: (p, q) %1 -> (q, p)
swapTensor = \(p,q) -> (q,p)

assocEither :: (a + b) + c %1 -> a + (b + c)
assocEither = \case
  Left (Left a) -> Left a
  Left (Right b) -> Right (Left b)
  Right c -> Right (Right c)

assocTensor :: ((a, b), c) %1 -> (a, (b, c))
assocTensor = \((a, b), c) -> (a, (b, c))

assocWith :: (a & b) & c %1 -> a & (b & c)
assocWith = \abc -> with \case
      L -> withL (withL abc)
      R -> with \case
        L -> withR (withL abc)
        R -> withR abc

assocPar :: (a ⅋ b) ⅋ c %1 -> a ⅋ (b ⅋ c)
assocPar = \apb_c -> par \case
  L -> \(nb, nc) -> parL (parL apb_c nc) nb
  R -> \na -> par \case
    L -> \nc -> parR (parL apb_c nc) na
    R -> \nb -> parR apb_c (na,nb)

unassocWith :: a & (b & c) %1 -> (a & b) & c
unassocWith = \abc -> with \case
  L -> with \case
    L -> withL abc
    R -> withL (withR abc)
  R -> withR (withR abc)

unassocPar :: a ⅋ (b ⅋ c) %1 -> (a ⅋ b) ⅋ c
unassocPar = \a_bpc -> par \case
  L -> \nc -> par \case
    L -> \nb -> parL a_bpc (nb,nc)
    R -> \na -> parL (parR a_bpc na) nc
  R -> \(na,nb) -> parR (parR a_bpc na) nb

unassocEither :: a + (b + c) %1 -> (a + b) + c
unassocEither = \case
  Left a -> Left (Left a)
  Right (Left b) -> Left (Right b)
  Right (Right c) -> Right c

unassocTensor :: (a, (b, c)) %1 -> ((a, b), c)
unassocTensor = \(na,(nb,nc)) -> ((na,nb),nc)
