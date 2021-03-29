{-# language CPP #-}
{-# language BlockArguments #-}
{-# language DefaultSignatures #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language ExplicitNamespaces #-}
{-# language ImportQualifiedPost #-}
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
( Category(..)
, NiceCategory(..)
, Functor(..)
, Contravariant(..)
, Bifunctor(..)
, Profunctor(..)
, Semimonoidal(..)
, unassoc
, Monoidal(..)
, unlambda
, unrho
, Symmetric(..)
, SymmetricMonoidal
) where

import Control.Category qualified as C
import Data.Void
import Data.Kind
import Linear.Logic
import Linear.Logic.Ops
import Prelude.Linear hiding (id,(.))
#ifdef DEV
import Unsafe.Linear
#endif
import GHC.Types

-- Control.Category.Linear?
class Category p where
  id :: p a a
  (.) :: p b c %1 -> p a b %1 -> p a c

instance Category (FUN 'One) where
  id x = x
  f . g = \x -> f (g x)

class NiceCategory p where
  o :: (Lol l, Lol l') => l (p b c) (l' (p a b) (p a c))

{-
instance NiceCategory (FUN 'One) where
  o = lol \case
    L -> \nf -> apartR nf & \(a2b :-#> Nofun a nc) -> Nofun (a2b a) nc
    R -> \bc -> lol \case
      L -> \(Nofun a nc) -> _ a bc nc -- impossible, requires mapping nc back through b %1 -> c
      R -> _ bc
-}

instance Category (⊸) where
  id = Lol \case L -> id; R -> id
  f . g = Lol \case
    L -> \c -> runLol g L (runLol f L c)
    R -> \a -> runLol f R (runLol g R a)

instance NiceCategory (⊸) where
  o = lol \case
    L -> \nf -> apartR nf & \(a2b :-#> a :-#> nc) -> fun a2b a :-#> nc
    R -> \bc -> lol \case
      L -> \(a :-#> nc) -> a :-#> runLol bc L nc
      R -> (bc .)

instance Category (⧟) where
  id = Iso \case L -> id; R -> id
  f . g = Iso \case
    L -> runIso g L . runIso f L
    R -> runIso f R . runIso g R
  
instance NiceCategory (⧟) where
  o = lol \case
    L -> \nf -> apartR nf & \(iab :-#> niac) -> niac & \case
      ApartL na c -> ApartL (runLol (runIso iab L) L na) c
      ApartR a nc -> ApartR (runLol (runIso iab R) R a) nc
    R -> \bc -> lol \case
      L -> \case
        ApartL na c -> ApartL na (runLol (runIso bc L) R c)
        ApartR a nc -> ApartR a (runLol (runIso bc R) L nc)
      R -> (bc .)

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
    L -> \(Ur nb) -> Ur (contra' f nb)
    R -> \na2v -> whyNot \nb -> because na2v (contra' f nb)
  {-# inline fmap #-}

instance Prop a => Functor ((⊸) a) where
  fmap f = lol \case
    L -> \x -> x & \(a :-#> nb) -> a :-#> contra' f nb
    R -> linear \g -> lol \case
      L -> linear \nb -> contra' g (contra' f nb)
      R -> \a -> fun' f (fun' g a)

instance Prop a => Functor (Either a) where
  fmap f = lol \case
    L -> \nawnb -> with \case
      L -> withL nawnb
      R -> contra' f (withR nawnb)
    R -> \case
      Left a -> Left a
      Right x -> Right (fun f x)

instance Prop x => Functor ((,) x) where
  fmap f = lol \case
    L -> \nxpnb -> par \case
      L -> \a -> parL' nxpnb (fun f a)
      R -> \x -> contra' f (parR' nxpnb x)
    R -> \(x, a) -> (x, fun f a)
  {-# inline fmap #-}

instance Prop p => Functor ((&) p) where
  fmap f = lol \case
    L -> \case
      Left np -> Left np
      Right nb -> Right (contra' f nb)
    R -> \pwa -> with \case
      L -> withL pwa
      R -> fun f (withR pwa)

instance Prop a => Functor ((⅋) a) where
  fmap f = lol \case
    L -> \(na,nb) -> (na, contra' f nb)
    R -> \apa1 -> par \case
      L -> \nb -> parL' apa1 (contra' f nb)
      R -> \na -> fun f (parR' apa1 na)

class
  ( forall a. Prop a => Prop (f a)
  ) => Contravariant f where
  contramap :: (Prop a, Prop b) => (a ⊸ b) -> f b ⊸ f a

instance Prop a => Contravariant ((-#>) a) where
  contramap f = contra (fmap f)

class
  ( forall a. Prop a => Functor (t a)
  ) => Profunctor t where
  dimap
    :: (Prop a, Prop b, Prop c, Prop d)
    => (a ⊸ b)
    -> (c ⊸ d)
    -> t b c ⊸ t a d

instance Profunctor (⊸) where
  dimap f g = lol \case
    L -> linear \(a :-#> nd) -> fun' f a :-#> contra' g nd
    R -> linear \h -> g . h . f

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
      L -> contra' f (withL nbwnd)
      R -> contra' g (withR nbwnd)
    R -> \case
      Left a -> Left (fun f a)
      Right c -> Right (fun g c)

instance Bifunctor (,) where
  bimap f g = lol \case
    L -> \nbpnd -> par \case
      L -> linear \c -> contra' f (parL' nbpnd (fun g c))
      R -> linear \a -> contra' g (parR' nbpnd (fun f a))
    R -> \(a, c) -> (fun f a, fun g c)

instance Bifunctor (&) where
  bimap f g = lol \case
    L -> \case
      Left nb  -> Left (contra' f nb)
      Right nd -> Right (contra' g nd)
    R -> \awc -> with \case
      L -> fun f (withL' awc)
      R -> fun g (withR' awc)

instance Bifunctor (⅋) where
  bimap f g = lol \case
    L -> \(nb,nd) -> (contra' f nb, contra' g nd)
    R -> \apc -> par \case
      L -> \nd -> fun' f (parL' apc (contra' g nd))
      R -> \nb -> fun' g (parR' apc (contra' f nb))

class Bifunctor t => Semimonoidal t where
  assoc :: (Prop a, Prop b, Prop c, Iso iso) => t (t a b) c `iso` t a (t b c)

unassoc :: (Semimonoidal t, Iso iso, Prop a, Prop b, Prop c) => t a (t b c) `iso` t (t a b) c
unassoc = inv' assoc

class (Prop (I t), Semimonoidal t) => Monoidal t where
  type I t :: Type
  lambda :: (Prop a, Iso iso) => a `iso` t (I t) a
  rho :: (Prop a, Iso iso) => a `iso` t a (I t)

unlambda :: (Monoidal t, Prop a, Iso iso) => t (I t) a `iso` a
unlambda = inv' lambda

unrho :: (Monoidal t, Prop a, Iso iso) => t a (I t) `iso` a
unrho = inv' rho

class Symmetric t where
  swap :: (Prop a, Prop b, Iso iso) => t a b `iso` t b a

class (Symmetric t, Monoidal t) => SymmetricMonoidal t 

instance Semimonoidal Either where
  assoc = assocEither

instance Monoidal Either where
  type I Either = Void
  lambda = lambdaEither
  rho = rhoEither

instance Symmetric Either where
  swap = swapEither

instance SymmetricMonoidal Either

instance Semimonoidal (,) where
  assoc = assocTensor

instance Monoidal (,) where
  type I (,) = ()
  lambda = lambdaTensor
  rho = rhoTensor

instance Symmetric (,) where
  swap = swapTensor

instance SymmetricMonoidal (,)

instance Semimonoidal (&) where
  assoc = assocWith

instance Monoidal (&) where
  type I (&) = Top
  lambda = lambdaWith
  rho = rhoWith

instance Symmetric (&) where
  swap = swapWith 

instance SymmetricMonoidal (&)

instance Semimonoidal (⅋) where
  assoc = assocPar

instance Monoidal (⅋) where
  type I (⅋) = Bot
  lambda = lambdaPar 
  rho = rhoPar

instance Symmetric (⅋) where
  swap = swapPar
  {-# inline swap #-}

instance SymmetricMonoidal (⅋)

instance Symmetric (#) where
  swap = swapApart

instance Symmetric (⧟) where
  swap = inv

