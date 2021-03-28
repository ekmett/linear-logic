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
{-# language Trustworthy #-}
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

-- |
-- <https://arxiv.org/pdf/1805.07518.pdf Linear Logic for Constructive Mathematics>
-- by Michael Shulman provides a principled take on this topic. There he constructs
-- an embedding of an affine logic into an intuitionistic logic via a Chu construction.
--
-- However, that version of things was only able to express an 'affine logic' where
-- the pairs \(\top\) and @()@, \(\bot\) and @Void@ are made to coincide.
--
-- Reconstructing this technique on top of <https://arxiv.org/abs/1710.09756 Linear Haskell>
-- allows us to construct a full intuitionistic linear logic, while retaining Shulman's
-- style of refutation.
--
-- +------------------------+--------------------------+-----------------------+
-- |                        | Additive                 | Multiplicative        |
-- +========================+==========================+=======================+
-- | Conjunction            | @('&')@ w/ unit 'Top'    | @(,)@ w/ unit @()@    |
-- +------------------------+--------------------------+-----------------------+
-- | Disjunction            | 'Either' w/ unit 'Void'  | @('⅋')@ w/ unit 'Bot' |
-- +------------------------+--------------------------+-----------------------+
--
-- 'Either' (or @('+')@) takes the place of the traditional \(\oplus\)
--
-- '(,)' (or @('*')@) takes the place of the traditional \(\otimes\)
--
-- To use the alias for @('*')@, make sure to enable @{-# LANGUAGE NoStarIsType #-}@
--
-- Negative polarity connectives are 'GHC.Types.RuntimeRep' polymorphic,
-- but only currently have 'Prop' instances defined for ''LiftedRep'

module Linear.Logic
( Prop(Not,(!=))
-- additive conjunction, with
, type (&)(..), Top(..), type With, with, withL, withR
-- additive disjunction, oplus
, type (+), Void, Either(..)
-- multiplicative conjunction, (,)
, type (*) -- ()
-- multiplciative disjunction, par
, type (⅋)(..), Bot(..), type Par, par, parL, parR
-- refutable "lollipop" implication
, type (⊸), fun, unfun
-- primitive implication
, Nofun(..)
-- ! modality
, Ur(..), No(..)
, extractUr, duplicateUr
, weakenUr, distUr
, contractUr
-- ? modality
, WhyNot(..), because, Why(..), why
, returnWhyNot, joinWhyNot
-- Internals
, Y(..)
) where

import Data.Kind
import Data.Void
import GHC.Types
import Linear.Logic.Ur
import Linear.Logic.Y

class (Prop (Not a), Not (Not a) ~ a) => Prop (a :: TYPE k) where
  -- | \(a^\bot\). The type of refutations of \(a\)
  --
  -- \(a^{\bot^\bot} \) = \(a\)
  type Not (a :: TYPE k) = (c :: TYPE k) | c -> a
  -- | \(a\) and \(a^\bot\) together yield a contradiction.
  --
  -- @
  -- ('!=') :: a %1 -> 'Not' a %1 -> r
  -- @
  (!=) :: a %1 -> Not a %1 -> r

-- | The unit for multiplicative conjunction, \(\texttt{()}\)
--
-- \(\texttt{()}^\bot\) ≡ \(\bot\)
instance Prop () where
  type Not () = Bot
  () != Bot b = b
  {-# inline (!=) #-}

-- | The unit for additive disjunction, \(\texttt{Void}\)
--
-- \(\texttt{Void}^\bot\) ≡ \(\top\)
instance Prop Void where
  type Not Void = Top
  (!=) = \case
  {-# inline (!=) #-}

-- | 'Top' can hold any unwanted environment, which allows it to work
-- as a unit for @('&')@.
data Top where
  -- | 'Top' :: a %1 -> 'Top'
  Top :: a %1 -> Top

-- | 'Bot' acts as a unit for @('⅋')@
data Bot where
  Bot :: (forall a. a) %1 -> Bot

-- | The unit for additive conjunction, \(\top\)
--
-- \(\top^\bot\) ≡ \(\texttt{Void}\)
instance Prop Top where
  type Not Top = Void
  t != v = (\case) v t
  {-# inline (!=) #-}

-- | The unit for multiplicative disjunction, \(\bot\)
--
-- \(\bot^\bot\) ≡ \(\texttt{()}\)
instance Prop Bot where
  type Not Bot = ()
  Bot a != () = a
  {-# inline (!=) #-}

{-
-- | Used to request a given side from 'With' or 'Par'.
type role Y nominal nominal nominal
type Y :: i -> j -> k -> Type
data Y a b c where
  L :: Y a b a
  R :: Y a b b
-}

-- With can be runtime rep polymorphic
infixr 3 &
type role (&) nominal nominal
type (&) :: forall i j. TYPE i -> TYPE j -> Type
newtype a & b = With (forall k (c :: TYPE k). Y a b c -> c)
type With = (&)

-- | Introduce a @'With'/('&')@ connective.
--
-- Usage:
--
-- @
-- 'with' \case
--   'L' -> ...
--   'R' -> ...
-- @
--
-- @
-- 'with' :: (forall c. 'Y' a b c -> c) %1 -> a '&' b
-- @
with :: forall i j (a :: TYPE i) (b :: TYPE j). (forall k (c :: TYPE k). Y a b c -> c) %1 -> a & b
with = With
{-# inline with #-}

-- | Eliminate a @'With'/('&')@ connective and extract the left choice.
--
-- @
-- 'withL' ('with' \case 'L' -> x; 'R' -> y) ≡ x
-- @
--
-- @
-- 'withL' :: a '&' b %1 -> a
-- @
withL :: a & b %1 -> a
withL (With f) = f L
{-# inline withL #-}

-- | Eliminate a 'With'/('&') connective and extract the right choice.
--
-- @
-- 'withR' ('with' \case 'L' -> x; 'R' -> y) ≡ y
-- @
--
-- @
-- 'withR' :: a '&' b %1 -> b
-- @
withR :: a & b %1 -> b
withR (With f) = f R
{-# inline withR #-}

instance (Prop a, Prop b) => Prop (a & b) where
  type Not (a & b) = Not a + Not b
  w != Left a = withL w != a
  w != Right b = withR w != b
  {-# inline (!=) #-}

infixr 2 +
type (+) = Either

instance (Prop a, Prop b) => Prop (Either a b) where
  type Not (Either a b) = Not a & Not b
  Left a != w = a != withL w
  Right a != w = a != withR w
  {-# inline (!=) #-}

infixr 3 *
type (*) = (,)

infixr 2 ⅋
type (⅋) :: forall i j. TYPE i -> TYPE j -> Type
type role (⅋) nominal nominal
-- | \(\par\) is multiplicative disjunction.
newtype (a :: TYPE i) ⅋ (b :: TYPE j) = Par (forall k (c :: TYPE k). Y (Not b %1 -> a) (Not a %1 -> b) c -> c)

type Par = (⅋)

-- | Introduce a @'par'/('⅋')@ connective.
--
-- Usage:
--
-- @
-- 'par' \case
--   'L' -> ...
--   'R' -> ...
-- @
--
-- When developing using holes, you may want to temporarily substitute 'Linear.Logic.Unsafe.unsafePar'
-- until all the holes have been solved, then putting this in instead once everything typechecks.
--
-- @
-- 'par' :: (forall c. 'Y' ('Not' b %1 -> a) ('Not' a %1 -> b) c %1 -> c) %1 -> a '⅋' b
-- @
par
  :: forall i j (a :: TYPE i) (b :: TYPE j). 
  (forall k (c :: TYPE k). Y (Not b %1 -> a) (Not a %1 -> b) c -> c) %1 -> a ⅋ b
par = Par
{-# inline par #-}

-- | Eliminate a @'par'/('⅋')@ connective, given refutation of the @b@, supply proof of @a@.
--
-- @
-- 'parL' ('par' \case 'L' -> x; 'R' -> y) ≡ x
-- @
--
-- @
-- 'parL' :: a '⅋' b %1 -> 'Not' b %1 -> a
-- @
parL :: a ⅋ b %1 -> Not b %1 -> a
parL (Par p) = p L
{-# inline parL #-}

-- | Eliminate a @'par'/('⅋')@ connective, given refutation of the @a@, supply proof of @b@.
--
-- @
-- parR (par \case L -> x; R -> y) ≡ y
-- @
--
-- @
-- 'parR' :: a '⅋' b %1 -> 'Not' a %1 -> b
-- @
parR :: a ⅋ b %1 -> Not a %1 -> b
parR (Par p) = p R
{-# inline parR #-}

instance (Prop a, Prop b) => Prop (a * b) where
  type Not (a * b) = Not a ⅋ Not b
  (a, b) != p = a != parL p b
  {-# inline (!=) #-}

instance (Prop a, Prop b) => Prop (a ⅋ b) where
  type Not (a ⅋ b) = Not a * Not b
  p != (na, nb) = parR p na != nb
  {-# inline (!=) #-}

-- | This instance is for @(a %1 -> b)@ despite haddock's lies.
-- The injective type family on @Not@ forces me to use a flexible
-- instance, rather than have the instance self-improve
instance (Prop a, Prop b) => Prop (a %1 -> b) where
  type Not (a %1 -> b) = Nofun a b
  f != Nofun a nb = f a != nb
  {-# inline (!=) #-}

-- | The refutation of a linear haskell arrow.
data Nofun a b = Nofun a (Not b)

deriving stock instance (Show a, Show (Not b)) => Show (Nofun a b)
deriving stock instance (Read a, Read (Not b)) => Read (Nofun a b)
deriving stock instance (Eq a, Eq (Not b)) => Eq (Nofun a b)
deriving stock instance (Ord a, Ord (Not b)) => Ord (Nofun a b)

instance (Prop a, Prop b) => Prop (Nofun a b) where
  type Not (Nofun a b) = a %1 -> b
  Nofun a nb != f = f a != nb
  {-# inline (!=) #-}

-- | \(\multimap\) is defined in terms of \(⅋\)
type p ⊸ q = Not p ⅋ q
infixr 0 ⊸

-- | Derive a linear function from a linear logic impliciation.
--
-- @
-- 'fun' :: forall a b. 'Prop' a => (a '⊸' b) %1 -> a %1 -> b
-- @
fun :: forall a b. Prop a => (a ⊸ b) %1 -> a %1 -> b
fun (Par p) = p R
{-# inline fun #-}

-- | Derive a linear function for the contrapositive from a
-- linear logic impliciation.
--
-- @
-- 'unfun' :: forall a b. 'Prop' a => (a '⊸' b) %1 -> a %1 -> b
-- @
unfun :: forall a b. (a ⊸ b) %1 -> Not b %1 -> Not a
unfun (Par p) = p L
{-# inline unfun #-}

-- | Heyting negation
newtype No a = No (forall r. a -> r)

-- | The exponential, or unrestricted modality, \( !a \)
--
-- This embeds arbitrary non-linear Haskell values into 'Prop'.
instance Prop (Ur a) where
  type Not (Ur a) = No a
  Ur a != No f = f a
  {-# inline (!=) #-}

-- | Heyting negation, used as a refutation of the exponential
instance Prop (No a) where
  type Not (No a) = Ur a
  No f != Ur a = f a
  {-# inline (!=) #-}

{-
funPar :: forall a b. Prop a => (a %1 -> b) %1 -> a ⊸ b
funPar = Unsafe.toLinear go where
  go :: (a %1 -> b) -> Not a ⅋ b
  go f = Par $ With \case
    R -> f
    L -> _ -- impossible as expected
-}

-- |
-- @
-- 'weakenUr' :: forall p q. 'Prop' p => p ⊸ ('Ur' q ⊸ p)
-- @
weakenUr :: forall p q. Prop p => p ⊸ (Ur q ⊸ p)
weakenUr = par \case
  L -> \(Ur{}, np) -> np
  R -> \p -> par \case
    L -> \q -> p != q
    R -> \Ur{} -> p
{-# inline weakenUr #-}

distUr :: forall p q. Prop p => Ur (p ⊸ q) ⊸ (Ur p ⊸ Ur q)
distUr = par \case
  L -> \(Ur p, No nq) -> No \nppq -> nq (parR nppq p)
  R -> \(Ur nppq) -> par \case
    L -> \(No nq) -> No \p -> nq (parR nppq p)
    R -> \(Ur p) -> Ur (parR nppq p)
{-# inline distUr #-}

extractUr :: forall p. Prop p => Ur p ⊸ p
extractUr = par \case
  L -> \np -> No \p -> np != p
  R -> \(Ur p) -> p
{-# inline extractUr #-}

duplicateUr :: forall p. Ur p ⊸ Ur (Ur p)
duplicateUr = par \case
  L -> \(No f) -> No \p -> f (Ur p)
  R -> \(Ur p) -> Ur (Ur p)
{-# inline duplicateUr #-}

contractUr :: (Prop p, Prop q) => (Ur p ⊸ Ur p ⊸ q) ⊸ Ur p ⊸ q
contractUr = par \case
  L -> \(Ur p, nq) -> (Ur p, (Ur p, nq))
  R -> \x -> par \case
    L -> \nq -> No \p -> parL (parR x (Ur p)) nq != Ur p
    R -> \(Ur p) -> parR (parR x (Ur p)) (Ur p)
{-# inline contractUr #-}

-- | The \(?a\) or "why not?" modality.
type role WhyNot nominal
newtype WhyNot a = WhyNot (forall r. Not a %1 -> r)

because :: WhyNot a %1 -> Not a %1 -> r
because (WhyNot a) = a
{-# inline because #-}

type role Why nominal
-- | The refutation of \(?a\)
newtype Why a = Why (Not a)

why :: Why a %1 -> Not a
why (Why x) = x
{-# inline why #-}

instance Prop a => Prop (WhyNot a) where
  type Not (WhyNot a) = Why a
  WhyNot f != Why x = f x
  {-# inline (!=) #-}

instance Prop a => Prop (Why a) where
  type Not (Why a) = WhyNot a
  Why x != WhyNot f = f x
  {-# inline (!=) #-}
 

returnWhyNot :: forall p. Prop p => p ⊸ WhyNot p
returnWhyNot = par \case
  L -> \x -> why x
  R -> \p -> WhyNot (p !=)
{-# inline returnWhyNot #-}

joinWhyNot :: forall p. Prop p => WhyNot (WhyNot p) ⊸ WhyNot p
joinWhyNot = par \case
  L -> Why
  R -> \f -> WhyNot \x -> because f (Why x)
{-# inline joinWhyNot #-}
