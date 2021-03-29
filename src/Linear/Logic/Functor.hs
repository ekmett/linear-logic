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
) where

import Data.Void
import Data.Kind
import Linear.Logic
import Linear.Logic.Ops
import Prelude hiding (Functor)
-- import Linear.Logic.Unsafe

class
  ( forall a. Prop a => Prop (f a)
  ) => Functor f where
  fmap :: (Prop a, Prop b) => (a ⊸ b) -> f a ⊸ f b

instance Functor Ur where
  fmap f = lol \case
    L -> \(No cb) -> No \a -> cb (fun f a)
    R -> \(Ur a) -> Ur (fun f a)
  {-# inline fmap #-}

instance Functor WhyNot where
  fmap f = lol \case
    L -> \nb -> why (unfun f (runWhy nb))
    R -> \na2v -> whyNot \nb -> because na2v (unfun f nb)
  {-# inline fmap #-}

instance Prop a => Functor (Either a) where
  fmap f = lol \case
    L -> \nawnb -> with \case
      L -> withL nawnb
      R -> unfun f (withR nawnb)
    R -> \case
      Left a -> Left a
      Right x -> Right (fun f x)

instance Prop x => Functor ((,) x) where
  fmap f = lol \case
    L -> \nxpnb -> par \case
      L -> \a -> parL nxpnb (fun f a)
      R -> \x -> unfun f (parR nxpnb x)
    R -> \(x, a) -> (x, fun f a)
  {-# inline fmap #-}

instance Prop p => Functor ((&) p) where
  fmap f = lol \case
    L -> \case
      Left np -> Left np
      Right nb -> Right (unfun f nb)
    R -> \pwa -> with \case
      L -> withL pwa
      R -> fun f (withR pwa)

instance Prop a => Functor ((⅋) a) where
  fmap f = lol \case
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
  contramap f = lol \case
    L -> \(Ur a) -> Ur (fun f a)
    R -> \(No cb) -> No \a -> cb (fun f a)
  {-# inline contramap #-}

instance Contravariant Why where
  contramap f = lol \case
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
  bimap f g = lol \case
    L -> \nbwnd -> with \case
      L -> unfun f (withL nbwnd)
      R -> unfun g (withR nbwnd)
    R -> \case
      Left a -> Left (fun f a)
      Right c -> Right (fun g c)

instance Bifunctor (,) where
  bimap f g = lol \case
    L -> \nbpnd -> par \case
      L -> \c -> unfun f (parL nbpnd (fun g c))
      R -> \a -> unfun g (parR nbpnd (fun f a))
    R -> \(a, c) -> (fun f a, fun g c)

instance Bifunctor (&) where
  bimap f g = lol \case
    L -> \case
      Left nb  -> Left  (unfun f nb)
      Right nd -> Right (unfun g nd)
    R -> \awc -> with \case
      L -> fun f (withL awc)
      R -> fun g (withR awc)

instance Bifunctor (⅋) where
  bimap f g = lol \case
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
  assoc = lol \case
    L -> unassocWith
    R -> assocEither
  unassoc = contra assoc

instance Monoidal Either where
  type I Either = Void
  lambda = lol \case
    L -> unlambdaWith
    R -> lambdaEither
  unlambda = contra lambda
  rho = lol \case
    L -> unrhoWith
    R -> rhoEither
  unrho = contra rho

instance SymmetricMonoidal Either where
  swap = lol \case
    L -> swapWith
    R -> swapEither

instance Semimonoidal (,) where
  assoc = lol \case
    L -> unassocPar
    R -> assocTensor
  unassoc = contra assoc

instance Monoidal (,) where
  type I (,) = ()
  lambda = lol \case
    L -> unlambdaPar
    R -> lambdaTensor
  unlambda = contra lambda
  rho = lol \case
    L -> unrhoPar 
    R -> rhoTensor
  unrho = contra rho

instance SymmetricMonoidal (,) where
  swap = lol \case
    L -> swapPar
    R -> swapTensor

instance Semimonoidal (&) where
  assoc = lol \case
    L -> unassocEither
    R -> assocWith
  unassoc = contra assoc

instance Monoidal (&) where
  type I (&) = Top
  lambda = lol \case
    L -> unlambdaEither
    R -> lambdaWith
  unlambda = contra lambda
  rho = lol \case
    L -> unrhoEither
    R -> rhoWith
  unrho = contra rho

instance SymmetricMonoidal (&) where
  swap = lol \case
    L -> swapEither
    R -> swapWith

instance Semimonoidal (⅋) where
  assoc = lol \case
    L -> unassocTensor
    R -> assocPar
  unassoc = contra assoc

instance Monoidal (⅋) where
  type I (⅋) = Bot
  lambda = lol \case
    L -> unlambdaTensor
    R -> lambdaPar 
  unlambda = contra lambda
  rho = lol \case
    L -> unrhoTensor
    R -> rhoPar 
  unrho = contra rho

instance SymmetricMonoidal (⅋) where
  swap = lol \case
    L -> swapTensor
    R -> swapPar
  {-# inline swap #-}

