{-# language BlockArguments #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language ExplicitNamespaces #-}
{-# language FlexibleContexts #-}
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
, Bifunctor(..)
, Monoidal(..)
, SymmetricMonoidal(..)
) where

import Data.Void
import Data.Kind
import Linear.Logic
import Prelude hiding (Functor)
-- import Unsafe.Linear as Unsafe

class (forall a. Prop a => Prop (f a)) => Functor f where
  fmap :: (Prop a, Prop b) => (a ⊸ b) -> f a ⊸ f b

{-
instance Functor Ur where
  fmap f = par \case
    L -> _ -- \nob -> _ -- No \a -> _
    R -> _
-}

instance Prop x => Functor ((*) x) where
  fmap f = par \case
    L -> \nxpnb -> par \case
      L -> \a -> parL nxpnb (fun f a)
      R -> \x -> unfun f (parR nxpnb x)
    R -> \(x, a) -> (x, fun f a)

-- prop data bifunctor
class
  ( forall a. Prop a => Functor (t a)
  ) => Bifunctor t where
  bimap
    :: (Prop a, Prop b, Prop c, Prop d)
    => (a ⊸ b)
    -> (c ⊸ d)
    -> t a c ⊸ t b d

class (Prop (I t), Bifunctor t) => Monoidal t where
  type I t :: Type
  assoc :: (Prop a, Prop b, Prop c) => t (t a b) c %1 -> t a (t b c)
  unassoc :: (Prop a, Prop b, Prop c) => t a (t b c) %1 -> t (t a b) c
  lambda :: Prop a => a %1 -> t (I t) a
  unlambda :: Prop a => t (I t) a %1 -> a
  rho :: Prop a => a %1 -> t a (I t)
  unrho :: Prop a => t a (I t) %1 -> a

class Monoidal t => SymmetricMonoidal t where
  swap :: (Prop a, Prop b) => t a b %1 -> t b a

instance Prop a => Functor (Either a) where
  fmap f = par \case
    L -> \nawnb -> with \case
      L -> withL nawnb
      R -> unfun f (withR nawnb)
    R -> \case
      Left a -> Left a
      Right x -> Right (fun f x)

instance Bifunctor Either where
  bimap f g = par \case
    L -> \nbwnd -> with \case
      L -> unfun f (withL nbwnd)
      R -> unfun g (withR nbwnd)
    R -> \case
      Left a -> Left (fun f a)
      Right c -> Right (fun g c)

instance Monoidal Either where
  type I Either = Void
  assoc = \case
    Left (Left a) -> Left a
    Left (Right b) -> Right (Left b)
    Right c -> Right (Right c)
  unassoc = \case
    Left a -> Left (Left a)
    Right (Left b) -> Left (Right b)
    Right (Right c) -> Right c
  lambda = Right
  unlambda = \case
    Left v -> \case{} v
    Right b -> b
  rho = Left
  unrho = \case
    Left a -> a
    Right v -> \case{} v

instance SymmetricMonoidal Either where
  swap = \case
    Left b -> Right b
    Right a -> Left a

instance Bifunctor (,) where
  bimap f g = par \case
    L -> \nbpnd -> par \case
      L -> \c -> unfun f (parL nbpnd (fun g c))
      R -> \a -> unfun g (parR nbpnd (fun f a))
    R -> \(a, c) -> (fun f a, fun g c)

instance Monoidal (,) where
  type I (,) = ()
  assoc ((a,b),c) = (a,(b,c))
  unassoc (a,(b,c)) = ((a,b),c)
  lambda = ((),)
  unlambda ((),a) = a
  rho = (,())
  unrho (a,()) = a

instance SymmetricMonoidal (,) where
  swap (a, b) = (b, a)

instance Prop p => Functor ((&) p) where
  fmap f = par \case
    L -> \case
      Left np -> Left np
      Right nb -> Right (unfun f nb)
    R -> \pwa -> with \case
      L -> withL pwa
      R -> fun f (withR pwa)

instance Bifunctor (&) where
  bimap f g = par \case
    L -> \case
      Left nb  -> Left  (unfun f nb)
      Right nd -> Right (unfun g nd)
    R -> \awc -> with \case
      L -> fun f (withL awc)
      R -> fun g (withR awc)

instance Monoidal (&) where
  type I (&) = Top
  assoc abc = with \case
    L -> withL (withL abc)
    R -> with \case
      L -> withR (withL abc)
      R -> withR abc
  unassoc abc = with \case
    L -> with \case
      L -> withL abc
      R -> withL (withR abc)
    R -> withR (withR abc)
  lambda a = with \case
    L -> Top a
    R -> a
  unlambda = withR
  rho b = with \case
    L -> b
    R -> Top b
  unrho = withL

instance SymmetricMonoidal (&) where
  swap w = with \case
    L -> withR w
    R -> withL w

instance Prop a => Functor ((⅋) a) where
  fmap f = par \case
    L -> \(na,nb) -> (na, unfun f nb)
    R -> \apa1 -> par \case
      L -> \nb -> parL apa1 (unfun f nb)
      R -> \na -> fun f (parR apa1 na)

instance Bifunctor (⅋) where
  bimap f g = par \case
    L -> \(nb,nd) -> (unfun f nb, unfun g nd)
    R -> \apc -> par \case
      L -> \nd -> fun f (parL apc (unfun g nd))
      R -> \nb -> fun g (parR apc (unfun f nb))

instance Monoidal (⅋) where
  type I (⅋) = Bot
  assoc apb_c = par \case
    L -> \(nb, nc) -> parL (parL apb_c nc) nb
    R -> \na -> par \case
      L -> \nc -> parR (parL apb_c nc) na
      R -> \nb -> parR apb_c (na,nb)
  unassoc a_bpc = par \case
    L -> \nc -> par \case
      L -> \nb -> parL a_bpc (nb,nc)
      R -> \na -> parL (parR a_bpc na) nc
    R -> \(na,nb) -> parR (parR a_bpc na) nb
  lambda a = par \case
    L -> \na -> a != na
    R -> \() -> a
  unlambda bpa = parR bpa ()
  rho b = par \case
    L -> \() -> b
    R -> \nb -> b != nb
  unrho apb = parL apb ()

instance SymmetricMonoidal (⅋) where
  swap apb = par \case
    L -> \na -> parR apb na
    R -> \nb -> parL apb nb
