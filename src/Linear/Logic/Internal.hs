{-# language BlockArguments #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
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

module Linear.Logic.Internal where

import Data.Kind
import Data.Void
import Linear.Logic.Ur
import Prelude hiding (Functor)

class (Prop (Not a), Not (Not a) ~ a) => Prop a where
  -- | \(a^\bot\). The type of refutations of \(a\)
  type Not a = c | c -> a
  -- | \(a\) and \(a^\bot\) together yield a contradiction.
  (!=) :: a %1 -> Not a %1 -> r

-- | The unit for multiplicative conjunction, \(\texttt{()}\)
--
-- \(\texttt{()}^\bot\) ≡ \(\bot\)
instance Prop () where
  type Not () = Bot
  () != Bot b = b

-- | The unit for additive disjunction, \(\texttt{Void}\)
--
-- \(\texttt{Void}^\bot\) ≡ \(\top\)
instance Prop Void where
  type Not Void = Top
  (!=) = \case

data Top where
  Top :: a %1 -> Top

data Bot where
  Bot :: (forall a. a) %1 -> Bot

-- | The unit for additive conjunction, \(\top\)
--
-- \(\top^\bot\) ≡ \(\texttt{Void}\)
instance Prop Top where
  type Not Top = Void
  t != v = (\case) v t

-- | The unit for multiplicative disjunction, \(\bot\)
--
-- \(\bot^\bot\) ≡ \(\texttt{()}\)
instance Prop Bot where
  type Not Bot = ()
  Bot a != () = a

-- TODO: allow representational roles by using Coercible a a'?
type role Y nominal nominal nominal
data Y a b c where
  L :: Y a b a
  R :: Y a b b

type role (&) nominal nominal
newtype a & b = With (forall c. Y a b c -> c)

with :: (forall c. Y a b c -> c) %1 -> a & b
with = With

infixr 3 &
type With = (&)

withL :: a & b %1 -> a
withL (With f) = f L

withR :: a & b %1 -> b
withR (With f) = f R

instance (Prop a, Prop b) => Prop (a & b) where
  type Not (a & b) = Not a + Not b
  w != Left a = withL w != a
  w != Right b = withR w != b

infixr 2 +
type (+) = Either

instance (Prop a, Prop b) => Prop (Either a b) where
  type Not (Either a b) = Not a & Not b
  Left a != w = a != withL w
  Right a != w = a != withR w

infixr 3 *
type (*) = (,)

infixr 2 ⅋
type role (⅋) nominal nominal
-- | \(\par\) is multiplicative disjunction.
newtype a ⅋ b = Par (forall c. Y (Not b %1 -> a) (Not a %1 -> b) c %1 -> c)

type Par = (⅋)

par :: (forall c. Y (Not b %1 -> a) (Not a %1 -> b) c %1 -> c) %1 -> a ⅋ b
par = Par

runPar :: a ⅋ b %1 -> Y (Not b %1 -> a) (Not a %1 -> b) c %1 -> c
runPar (Par p) y = p y

parL :: a ⅋ b %1 -> Not b %1 -> a
parL (Par p) = p L

parR :: a ⅋ b %1 -> Not a %1 -> b
parR (Par p) = p R

instance (Prop a, Prop b) => Prop (a * b) where
  type Not (a * b) = Not a ⅋ Not b
  (a, b) != p = a != parL p b

instance (Prop a, Prop b) => Prop (a ⅋ b) where
  type Not (a ⅋ b) = Not a * Not b
  p != (na, nb) = parR p na != nb

-- p ⊸ q = Not p ⅋ q = With (Not b %1 -> Not a) (a %1 -> b)
-- Not (p ⊸ q) = Not (Not p ⅋ q) = (p, Not q)
-- Not (p, Not q) = Not p ⅋ q = p ⊸ q
  
-- | This instance is for @(a %1 -> b)@ despite haddock's lies.
-- The injective type family on @Not@ forces me to use a flexible
-- instance, rather than have the instance self-improve
instance (Prop a, Prop b) => Prop (a %1 -> b) where
  type Not (a %1 -> b) = Nofun a b
  f != Nofun a nb = f a != nb

data Nofun a b = Nofun a (Not b)

deriving stock instance (Show a, Show (Not b)) => Show (Nofun a b)
deriving stock instance (Read a, Read (Not b)) => Read (Nofun a b)
deriving stock instance (Eq a, Eq (Not b)) => Eq (Nofun a b)
deriving stock instance (Ord a, Ord (Not b)) => Ord (Nofun a b)

instance (Prop a, Prop b) => Prop (Nofun a b) where
  type Not (Nofun a b) = a %1 -> b
  Nofun a nb != f = f a != nb

-- | \(\multimap\) is defined in terms of \(\parr\)
type p ⊸ q = Not p ⅋ q
infixr 0 ⊸

fun :: forall a b. Prop a => (a ⊸ b) %1 -> a %1 -> b
fun (Par p) = p R

unfun :: forall a b. (a ⊸ b) %1 -> Not b %1 -> Not a
unfun (Par p) = p L

-- | Heyting negation
newtype No a = No { runNo :: forall r. Ur a %1 -> r }

-- | The exponential, or unrestricted modality, \( !a \)
--
-- This embeds arbitrary non-linear Haskell values into 'Prop'.
instance Prop (Ur a) where
  type Not (Ur a) = No a
  a != No f = f a

-- | Heyting negation, used as a refutation of the exponential
instance Prop (No a) where
  type Not (No a) = Ur a 
  No f != a = f a

{-
funPar :: forall a b. Prop a => (a %1 -> b) %1 -> a ⊸ b
funPar = Unsafe.toLinear go where
  go :: (a %1 -> b) -> Not a ⅋ b
  go f = Par $ With \case 
    R -> f
    L -> _ -- impossible as expected
-}

weakenUr :: forall p q. Prop p => p ⊸ (Ur q ⊸ p)
weakenUr = par \case
  L -> \(Ur{}, np) -> np
  R -> \p -> par \case 
    L -> \q -> p != q
    R -> \Ur{} -> p
 
distUr :: forall p q. Prop p => Ur (p ⊸ q) ⊸ (Ur p ⊸ Ur q)
distUr = par \case
  L -> \(Ur p, No nq) -> No \(Ur nppq) -> nq (Ur (parR nppq p))
  R -> \(Ur nppq) -> par \case
    L -> \(No nq) -> No \(Ur p) -> nq (Ur (parR nppq p))
    R -> \(Ur p) -> Ur (parR nppq p)

extractUr :: forall p. Prop p => Ur p ⊸ p
extractUr = par \case
  L -> \np -> No \(Ur p) -> np != p
  R -> \(Ur p) -> p

duplicateUr :: forall p. Ur p ⊸ Ur (Ur p)
duplicateUr = par \case
  L -> \(No f) -> No \(Ur p) -> f (Ur (Ur p))
  R -> \(Ur p) -> Ur (Ur p)

contraction :: (Prop p, Prop q) => (Ur p ⊸ Ur p ⊸ q) ⊸ Ur p ⊸ q
contraction = par \case
  L -> \(Ur p, nq) -> (Ur p, (Ur p, nq))
  R -> \x -> par \case
    L -> \nq -> No \(Ur p) -> parL (parR x (Ur p)) nq != Ur p
    R -> \(Ur p) -> parR (parR x (Ur p)) (Ur p)

-- | The \(?a\) or "why not?" modality.
type role WhyNot nominal
newtype WhyNot a = WhyNot (forall r. Not a %1 -> r)

because :: WhyNot a %1 -> Not a %1 -> r
because (WhyNot a) = a

type role Why nominal
-- | The refutation of \(?a\)
newtype Why a = Why (Not a)

why :: Why a %1 -> Not a
why (Why x) = x

instance Prop a => Prop (WhyNot a) where
  type Not (WhyNot a) = Why a
  WhyNot f != Why x = f x
  
instance Prop a => Prop (Why a) where
  type Not (Why a) = WhyNot a
  Why x != WhyNot f = f x

returnWhyNot :: forall p. Prop p => p ⊸ WhyNot p
returnWhyNot = par \case
  L -> \x -> why x
  R -> \p -> WhyNot (p !=)

joinWhyNot :: forall p. Prop p => WhyNot (WhyNot p) ⊸ WhyNot p
joinWhyNot = par \case
  L -> Why
  R -> \f -> WhyNot \x -> because f (Why x)

class (forall a. Prop a => Prop (f a)) => Functor f where
  fmap :: (Prop a, Prop b) => (a ⊸ b) -> f a ⊸ f b

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
