{-# language CPP #-}
{-# language BlockArguments #-}
{-# language DefaultSignatures #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language ExplicitNamespaces #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language LinearTypes #-}
{-# language NoImplicitPrelude #-}
{-# language NoStarIsType #-}
{-# language PolyKinds #-}
{-# language QuantifiedConstraints #-}
{-# language RankNTypes #-}
{-# language RoleAnnotations #-}
{-# language ScopedTypeVariables #-}
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

#define DEV
#ifdef DEV
{-# language Trustworthy #-}
{-# options_ghc -Wno-unused-imports #-}
#else
{-# language Safe #-}
#endif

module Linear.Logic.Functor
( Functor(..)
, Contravariant(..)
, Bifunctor(..)
, Semimonoidal(..)
, Monoidal(..)
, Symmetric(..)
, SymmetricMonoidal
) where

import Data.Void
import Data.Kind
import Linear.Logic
import Linear.Logic.Ops
import Prelude.Linear
#ifdef DEV
import Unsafe.Linear
#endif
import GHC.Types

class
  ( forall a. Prop a => Prop (f a)
  ) => Functor f where
  fmap :: (Prop a, Prop b) => (a ⊸ b) -> f a ⊸ f b

instance Functor Ur where
  fmap f = lol \case
    L -> \(WhyNot cb) -> WhyNot \a -> cb (fun f a)
    R -> \(Ur a) -> Ur (fun f a)
  {-# inline fmap #-}

instance Functor WhyNot where
  fmap f = lol \case
    L -> \(Ur nb) -> Ur (contra f nb)
    R -> \na2v -> whyNot \nb -> because na2v (contra f nb)
  {-# inline fmap #-}

instance Prop a => Functor ((⊸) a) where
  fmap f = lol \case
    L -> \x -> x & \(a :-#> nb) -> a :-#> contra' f nb
    R -> \g -> lol \case
      L -> \nb -> contra' g (contra' f nb)
      R -> \a -> fun' f (fun' g a)

instance Prop a => Functor (Either a) where
  fmap f = lol \case
    L -> \nawnb -> with \case
      L -> withL nawnb
      R -> contra f (withR nawnb)
    R -> \case
      Left a -> Left a
      Right x -> Right (fun f x)

instance Prop x => Functor ((,) x) where
  fmap f = lol \case
    L -> \nxpnb -> par \case
      L -> \a -> parL' nxpnb (fun f a)
      R -> \x -> contra f (parR' nxpnb x)
    R -> \(x, a) -> (x, fun f a)
  {-# inline fmap #-}

instance Prop p => Functor ((&) p) where
  fmap f = lol \case
    L -> \case
      Left np -> Left np
      Right nb -> Right (contra f nb)
    R -> \pwa -> with \case
      L -> withL pwa
      R -> fun f (withR pwa)

instance Prop a => Functor ((⅋) a) where
  fmap f = lol \case
    L -> \(na,nb) -> (na, contra f nb)
    R -> \apa1 -> par \case
      L -> \nb -> parL' apa1 (contra f nb)
      R -> \na -> fun f (parR' apa1 na)

class
  ( forall a. Prop a => Prop (f a)
  ) => Contravariant f where
  contramap :: (Prop a, Prop b) => (a ⊸ b) -> f b ⊸ f a

instance Prop a => Contravariant ((-#>) a) where
  contramap f = contra (fmap f)

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
      L -> contra f (withL nbwnd)
      R -> contra g (withR nbwnd)
    R -> \case
      Left a -> Left (fun f a)
      Right c -> Right (fun g c)

instance Bifunctor (,) where
  bimap f g = lol \case
    L -> \nbpnd -> par \case
      L -> \c -> contra @(%->) f (parL' nbpnd (fun g c))
      R -> \a -> contra @(%->) g (parR' nbpnd (fun f a))
    R -> \(a, c) -> (fun f a, fun g c)

instance Bifunctor (&) where
  bimap f g = lol \case
    L -> \case
      Left nb  -> Left  (contra f nb)
      Right nd -> Right (contra g nd)
    R -> \awc -> with \case
      L -> fun f (withL' awc)
      R -> fun g (withR' awc)

instance Bifunctor (⅋) where
  bimap f g = lol \case
    L -> \(nb,nd) -> (contra f nb, contra g nd)
    R -> \apc -> par \case
      L -> \nd -> fun' f (parL' apc (contra g nd))
      R -> \nb -> fun' g (parR' apc (contra f nb))

class Bifunctor t => Semimonoidal t where
  assoc :: (Prop a, Prop b, Prop c, Iso l) => t (t a b) c `l` t a (t b c)

class (Prop (I t), Semimonoidal t) => Monoidal t where
  type I t :: Type
  lambda :: (Prop a, Iso l) => a `l` t (I t) a
  rho :: (Prop a, Iso l) => a `l` t a (I t)

class Symmetric t where
  swap :: (Prop a, Prop b, Iso l) => t a b `l` t b a

class (Symmetric t, Monoidal t) => SymmetricMonoidal t 

instance Semimonoidal Either where
  assoc = iso \case
    L -> lol \case
      L -> assocWith'
      R -> unassocEither'
    R -> lol \case
      L -> unassocWith'
      R -> assocEither'

instance Monoidal Either where
  type I Either = Void
  lambda = iso \case
    L -> lol \case
      L -> lambdaWith'
      R -> unlambdaEither'
    R -> lol \case
      L -> unlambdaWith'
      R -> lambdaEither'
  rho = iso \case
    L -> lol \case
      L -> rhoWith'
      R -> unrhoEither'
    R -> lol \case
      L -> unrhoWith'
      R -> rhoEither'

instance Symmetric Either where
  swap = iso \case
    L -> lol \case
      L -> swapWith'
      R -> swapEither'
    R -> lol \case
      L -> swapWith'
      R -> swapEither'

instance SymmetricMonoidal Either

instance Semimonoidal (,) where
  assoc = iso \case
    L -> lol \case
      L -> assocPar'
      R -> unassocTensor'
    R -> lol \case
      L -> unassocPar'
      R -> assocTensor'

instance Monoidal (,) where
  type I (,) = ()
  lambda = iso \case
    L -> lol \case
      L -> lambdaPar'
      R -> unlambdaTensor'
    R -> lol \case
      L -> unlambdaPar'
      R -> lambdaTensor'
  rho = iso \case
    L -> lol \case
      L -> rhoPar'
      R -> unrhoTensor'
    R -> lol \case
      L -> unrhoPar'
      R -> rhoTensor'

instance Symmetric (,) where
  swap = iso \case
    L -> lol \case
      L -> swapPar'
      R -> swapTensor'
    R -> lol \case
      L -> swapPar'
      R -> swapTensor'

instance SymmetricMonoidal (,)

instance Semimonoidal (&) where
  assoc = iso \case
    L -> lol \case
      L -> assocEither'
      R -> unassocWith'
    R -> lol \case
      L -> unassocEither'
      R -> assocWith'

instance Monoidal (&) where
  type I (&) = Top
  lambda = iso \case
    L -> lol \case
      L -> lambdaEither'
      R -> unlambdaWith'
    R -> lol \case
      L -> unlambdaEither'
      R -> lambdaWith'
  rho = iso \case
    L -> lol \case
      L -> rhoEither'
      R -> unrhoWith'
    R -> lol \case
      L -> unrhoEither'
      R -> rhoWith'

instance Symmetric (&) where
  swap = iso \case
    L -> lol \case
      L -> swapEither'
      R -> swapWith'
    R -> lol \case
      L -> swapEither'
      R -> swapWith'

instance SymmetricMonoidal (&)

instance Semimonoidal (⅋) where
  assoc = iso \case
    L -> lol \case
      L -> assocTensor'
      R -> unassocPar'
    R -> lol \case
      L -> unassocTensor'
      R -> assocPar'

instance Monoidal (⅋) where
  type I (⅋) = Bot
  lambda = iso \case
    L -> lol \case
      L -> lambdaTensor'
      R -> unlambdaPar'
    R -> lol \case
      L -> unlambdaTensor'
      R -> lambdaPar'
  rho = iso \case
    L -> lol \case
      L -> rhoTensor'
      R -> unrhoPar'
    R -> lol \case
      L -> unrhoTensor'
      R -> rhoPar'

instance Symmetric (⅋) where
  swap = iso \case
    L -> lol \case
      L -> swapTensor'
      R -> swapPar'
    R -> lol \case
      L -> swapTensor'
      R -> swapPar'
  {-# inline swap #-}

instance SymmetricMonoidal (⅋)

inv' :: Iso iso => a ⧟ b %1 -> iso b a
inv' (Iso f) = iso \case
  L -> f R
  R -> f L
  
swapApart' :: a # b %1 -> b # a
swapApart' (ApartL na b) = ApartR b na
swapApart' (ApartR a nb) = ApartL nb a

swapApart'' :: Lol l => l (a # b) (b # a)
swapApart'' = lol \case
  L -> inv'
  R -> swapApart'

swapApart :: Iso iso => iso (a # b) (b # a)
swapApart = iso \case
  L -> swapApart''
  R -> swapApart''

instance Symmetric (#) where
  swap = swapApart

instance Symmetric (⧟) where
  swap = iso \case
    L -> lol \case
      L -> swapApart'
      R -> inv'
    R -> lol \case
      L -> swapApart'
      R -> inv'

