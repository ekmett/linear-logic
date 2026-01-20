{-# language BlockArguments #-}
{-# language ConstraintKinds #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language ExplicitNamespaces #-}
{-# language FlexibleContexts #-}
{-# language ViewPatterns #-}
{-# language FlexibleInstances #-}
{-# language DataKinds #-}
{-# language NoImplicitPrelude #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language LinearTypes #-}
{-# language NoStarIsType #-}
{-# language ImportQualifiedPost #-}
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
{-# options_haddock not-home #-}
{-# options_ghc -Wno-unused-imports #-} -- toLinear is too damn convenient while debugging to keep erasing it

-- | Core definitions for the linear logic embedding.
--
-- This module defines the basic proposition class, connectives, and
-- refutation machinery. It is exposed for advanced use, but most users
-- should prefer "Linear.Logic".
module Linear.Logic.Internal where

import Control.Applicative (Const(..))
import Control.Category qualified as C
import Data.Dependent.Sum
import Data.Kind
import Data.Void
import Data.Functor.Product
import Data.Functor.Sum
import Data.Type.Equality
import GHC.Generics
import GHC.Types
import Prelude.Linear hiding (Sum)
import Linear.Logic.Orphans ()
import Linear.Logic.Y
import Unsafe.Linear (toLinear)

-- | Evidence that 'Not' is involutive for @a@.
--
-- This is used to avoid passing dictionaries when they aren't needed.
type Prep a = Not (Not a) ~ a

-- | Propositions with a specified refutation type.
class Prep a => Prop' a where
  -- | \(a^\bot\). The type of refutations of \(a\)
  --
  -- \(a^{\bot^\bot} \) = \(a\)
  type Not a = c | c -> a
  -- | \(a\) and \(a^\bot\) together yield a contradiction.
  --
  -- @
  -- ('!=') :: a %1 -> 'Not' a %1 -> r
  -- @
  (!=) :: a %1 -> Not a %1 -> r

-- | A proposition whose refutation is also a proposition.
--
-- This avoids 'UndecidableSuperClasses' by splitting the constraint.
type Prop a = (Prop' a, Prop' (Not a))

-- | The unit for multiplicative conjunction, \(\texttt{()}\)
--
-- \(\texttt{()}^\bot\) ≡ \(\bot\)
instance Prop' () where
  type Not () = Bot
  x != Bot b = b (Top x)
  {-# inline (!=) #-}

-- | The unit for additive disjunction, \(\texttt{Void}\)
--
-- \(\texttt{Void}^\bot\) ≡ \(\top\)
instance Prop' Void where
  type Not Void = Top
  v != Top a = \case{} v a
  {-# inline (!=) #-}

-- | 'Top' can hold any unwanted environment, which allows it to work
-- as a unit for @('&')@.

data Top where
  -- | 'Top' :: a %1 -> 'Top'
  Top :: a %1 -> Top

-- | 'Bot' acts as a unit for @('⅋')@
--
-- Defined via ?0 = Bot = WhyNot Void = forall r. Not Void %1 -> r = (forall r. Top %1 -> r)
data Bot where
  Bot :: (forall a. Top %1 -> a) %1 -> Bot

instance Consumable Bot where
  consume (Bot f) = f (Top ())

instance Dupable Bot where
  dup2 (Bot f) = f (Top ())

-- | The unit for additive conjunction, \(\top\)
--
-- \(\top^\bot\) ≡ \(\texttt{Void}\)
instance Prop' Top where
  type Not Top = Void
  Top a != v = \case{} v a
  {-# inline (!=) #-}

-- | The unit for multiplicative disjunction, \(\bot\)
--
-- \(\bot^\bot\) ≡ \(\texttt{()}\)
instance Prop' Bot where
  type Not Bot = ()
  Bot a != x = a (Top x)
  {-# inline (!=) #-}

{-
-- | Used to request a given side from 'With' or 'Par'.
--
-- An unlifted version of this is suplied by Linear.Logic.Y
type role Y nominal nominal nominal
type Y :: i -> i -> i -> Type
data Y a b c where
  L :: Y a b a
  R :: Y a b b
-}

-- | Additive conjunction.
--
-- Laws: associative and commutative up to 'Iso', with unit 'Top'.
-- This is Church-encoded as a choice of side via 'Y'.
infixr 3 &
type role (&) nominal nominal
type (&) :: Type -> Type -> Type

newtype a & b = With (forall c. Y a b c -> c)

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
with :: (forall c. Y a b c -> c) %1 -> a & b
with = With
{-# inline with #-}

runWith :: a & b %1 -> Y a b c -> c
runWith (With f) = f

-- | Eliminate a @'With'/('&')@ connective and extract the left choice.
--
-- @
-- 'withL'' ('with' \case 'L' -> x; 'R' -> y) ≡ x
-- @
--
-- @
-- 'withL'' :: a '&' b %1 -> a
-- @
withL' :: a & b %1 -> a
withL' (With f) = f L
{-# inline withL' #-}

-- | Eliminate a 'With'/('&') connective and extract the right choice.
--
-- @
-- 'withR' ('with' \case 'L' -> x; 'R' -> y) ≡ y
-- @
--
-- @
-- 'withR' :: a '&' b %1 -> b
-- @
withR' :: a & b %1 -> b
withR' (With f) = f R
{-# inline withR' #-}

instance (Prop' a, Prop' b) => Prop' (a & b) where
  type Not (a & b) = Not a + Not b
  w != Left a = withL' w != a
  w != Right b = withR' w != b
  {-# inline (!=) #-}

-- | Additive disjunction.
--
-- Laws: associative and commutative up to 'Iso', with unit 'Void'.
-- This is a synonym for 'Either'.
infixr 2 +
type (+) = Either

instance (Prop' a, Prop' b) => Prop' (Either a b) where
  type Not (Either a b) = Not a & Not b
  Left a != w = a != withL' w
  Right a != w = a != withR' w
  {-# inline (!=) #-}

-- | Multiplicative conjunction.
--
-- Laws: associative and commutative up to 'Iso', with unit @()@.
-- This is a synonym for '(,)'.
infixr 3 *
type (*) = (,)

infixr 2 ⅋
type (⅋) :: Type -> Type -> Type
type role (⅋) nominal nominal
-- | \(\par\) is multiplicative disjunction.
--
-- Laws: associative and commutative up to 'Iso', with unit 'Bot'.
newtype a ⅋ b = Par (forall c. Y (Not b %1 -> a) (Not a %1 -> b) c -> c)

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
par :: (forall c. Y (Not b %1 -> a) (Not a %1 -> b) c -> c) %1 -> a ⅋ b
par = Par
{-# inline par #-}

-- | Eliminate a @'par'/('⅋')@ connective, given refutation of the @b@, supply proof of @a@.
--
-- @
-- 'parL'' ('par' \case 'L' -> x; 'R' -> y) ≡ x
-- @
--
-- @
-- 'parL'' :: a '⅋' b %1 -> 'Not' b %1 -> a
-- @
parL' :: a ⅋ b %1 -> Not b %1 -> a
parL' (Par p) = p L
{-# inline parL' #-}

-- | Eliminate a @'par'/('⅋')@ connective, given refutation of the @a@, supply proof of @b@.
--
-- @
-- parR (par \case L -> x; R -> y) ≡ y
-- @
--
-- @
-- 'parR' :: a '⅋' b %1 -> 'Not' a %1 -> b
-- @
parR' :: a ⅋ b %1 -> Not a %1 -> b
parR' (Par p) = p R
{-# inline parR' #-}

instance (Prop' a, Prep b) => Prop' (a * b) where
  type Not (a * b) = Not a ⅋ Not b
  (a, b) != p = a != parL' p b
  {-# inline (!=) #-}

instance (Prop' a, Prep b) => Prop' (a ⅋ b) where
  type Not (a ⅋ b) = Not a * Not b
  p != (a, b) = parL' p b != a
  {-# inline (!=) #-}

-- | This instance is for @(a %1 -> b)@ despite haddock's lies.
-- The injective type family on @Not@ forces me to use a flexible
-- instance, rather than have the instance self-improve
instance Prop' b => Prop' (a %m -> b) where
  type Not (a %m -> b) = Nofun m b a
  f != (Nofun a nb) = f a != nb
  {-# inline (!=) #-}

-- | Refutations of a linear Haskell arrow, matching the refutation of @a ⊸ b@.
data Nofun m b a where
  Nofun :: a %m -> Not b %1 -> Nofun m b a

deriving stock instance (Show a, Show (Not b)) => Show (Nofun m b a)
deriving stock instance (Read a, Read (Not b)) => Read (Nofun m b a)
-- deriving stock instance (Eq a, Eq (Not b)) => Eq (Nofun m a b)
-- deriving stock instance (Ord a, Ord (Not b)) => Ord (Nofun m a b)

instance Prop' b => Prop' (Nofun m b a) where
  type Not (Nofun m b a) = a %m -> b
  Nofun a nb != f = f a != nb
  {-# inline (!=) #-}

infixr 0 ⊸

type (%->) = FUN 'One

-- | \(\multimap\) could be defined in terms of \(⅋\), but then I couldn't hang instances off it.
--
-- type p ⊸ q = Not p ⅋ q

-- | Linear implication, encoded by a choice between proof and refutation.
--
-- Laws: contravariant in the domain and covariant in the codomain via
-- 'contra''.
newtype a ⊸ b = Lol (forall c. Y (Not b %1 -> Not a) (a %1 -> b) c -> c)

-- | Directed apartness, i.e. a refutation of @a ⊸ b@.
data b <#- a where (:-#>) :: a %1 -> Not b %1 -> b <#- a

-- data a -#> b where (:-#>) :: a %1 -> Not b %1 -> a -#> b
infixl 0 <#-
infixr 3 :-#>

-- | Symmetric notion of equivalence, encoded by a choice of direction.
--
-- Laws: involutive via 'inv' and symmetric via 'swap'.
newtype a ⧟ b = Iso (forall c. Y (b ⊸ a) (a ⊸ b) c -> c)
infixr 0 ⧟

runLol :: a ⊸ b %1 -> Y (Not b %1 -> Not a) (a %1 -> b) c -> c
runLol (Lol f) = f

runIso :: a ⧟ b %1 -> Y (b ⊸ a) (a ⊸ b) c -> c
runIso (Iso f) = f

-- | Sometimes linear haskell needs some help to infer that we really want linear usage.
linear :: (a %1 -> b) %1 -> a %1 -> b
linear = id

-- | Unsafely coerce multiplicities when inference is too strict.
unsafeLinear :: (a %p -> b) %1 -> a %q -> b
unsafeLinear = toLinear

instance C.Category (⊸) where
  id = Lol \case L -> id; R -> id
  f . g = Lol \case
    L -> linear \c -> runLol g L (runLol f L c)
    R -> linear \a -> runLol f R (runLol g R a)

instance C.Category (⧟) where
  id = Iso \case L -> C.id; R -> C.id
  f . g = Iso \case
    L -> runIso g L C.. runIso f L
    R -> runIso f R C.. runIso g R

-- | Apartness for isomorphisms.
data b # a
  = ApartL (Not a) b
  | ApartR a (Not b)

instance (Prop' a, Prop' b) => Prop' (a ⧟ b) where
  type Not (a ⧟ b) = b # a
  Iso f != ApartR a nb = f R != (a :-#> nb)
  Iso f != ApartL na b = f L != (b :-#> na)

instance (Prop' a, Prop' b) => Prop' (b # a) where
  type Not (b # a) = a ⧟ b
  ApartR a nb != Iso f = f R != (a :-#> nb)
  ApartL na b != Iso f = f L != (b :-#> na)

instance (Prep a, Prop' b) => Prop' (a ⊸ b) where
  type Not (a ⊸ b) = b <#- a
  f != (a :-#> nb) = runLol f R a != nb

instance (Prep a, Prop' b) => Prop' (b <#- a) where
  type Not (b <#- a) = a ⊸ b
  (a :-#> nb) != f = runLol f R a != nb

deriving stock instance (Show a, Show (Not b)) => Show (b <#- a)
deriving stock instance (Read a, Read (Not b)) => Read (b <#- a)
-- deriving stock instance (Eq a, Eq (Not b)) => Eq (a # b)
-- deriving stock instance (Ord a, Ord (Not b)) => Ord (a # b)

-- | The @?a@ or "why not?" modality.
--
-- Laws: dual to 'Ur' via 'Prop'' instances.
type role WhyNot nominal
newtype WhyNot a = WhyNot (forall r. Not a -> r)

whyNot :: (forall r. Not a -> r) %1 -> WhyNot a
whyNot = WhyNot

because :: WhyNot a %1 -> Not a -> r
because (WhyNot a) = a
{-# inline because #-}

-- | The exponential, or unrestricted modality, @!a@.
--
-- This embeds arbitrary non-linear Haskell values into 'Prop'.
instance Prep a => Prop' (Ur a) where
  type Not (Ur a) = WhyNot (Not a)
  Ur a != f = because f a
  {-# inline (!=) #-}

instance Prep a => Prop' (WhyNot a) where
  type Not (WhyNot a) = Ur (Not a)
  f != Ur a = because f a
  {-# inline (!=) #-}

-- | Experimental: dependent additives via 'Data.Dependent.Sum'.
--
-- @
-- data DSum f g where
--   (:=>) :: !(f a) -> g a -> DSum f g

-- DSum (Y a b) Identity ~ Either a b
-- DWith (Y a b) Identity ~ a & b
-- @
newtype DWith f g = DWith (forall x. f x %1 -> g x)

dwith :: (forall x. f x %1 -> g x) %1 -> DWith f g
dwith = DWith

runDWith :: DWith f g %1 -> f x %1 -> g x
runDWith (DWith f) = f

type IPrep f = INot (INot f) ~ f

-- | Experimental: indexed propositions.
class
  ( IPrep f
  , forall a. Prop' (f a)
  ) => IProp' (f :: i -> Type) where
  type INot (f :: i -> Type) = (c :: i -> Type) | c -> f
  icontradict :: f a %1 -> INot f a %1 -> r
  inot :: INot f a :~: Not (f a)

type IProp f = (IProp' f, IProp' (INot f))

instance Prop' a => IProp' (Const a) where
  type INot (Const a) = Const (Not a)
  inot = Refl
  icontradict (Const a) (Const na) = a != na

instance Prop' a => Prop' (Const a b) where
  type Not (Const a b) = Const (Not a) b
  Const a != Const na = a != na

instance IProp' g => Prop' (DWith f g) where
  type Not (DWith f g) = DSum f (INot g)
  h != (f :=> g) = icontradict (runDWith h f) g

instance IProp' g => Prop' (DSum f g) where
  type Not (DSum f g) = DWith f (INot g)
  (f :=> g) != h = icontradict g (runDWith h f)

type (:&:) :: forall i. (i -> Type) -> (i -> Type) -> i -> Type
newtype (:&:) f g a = IWith (forall h. Y f g h -> h a)

instance (IProp' f, IProp' g) => Prop' ((:&:) f g a) where
  type Not ((:&:) f g a) = (INot f :+: INot g) a
  (!=) (IWith f) = \case
    L1 g -> icontradict (f L) g
    R1 g -> icontradict (f R) g

instance (IProp' f, IProp' g) => Prop' ((:+:) f g a) where
  type Not ((:+:) f g a) = (INot f :&: INot g) a
  L1 g != IWith f = icontradict g (f L)
  R1 g != IWith f = icontradict g (f R)

instance (IProp' f, IProp' g) => IProp' (f :&: g) where
  type INot (f :&: g) = INot f :+: INot g
  icontradict (IWith f) = \case
    L1 g -> icontradict (f L) g
    R1 g -> icontradict (f R) g
  inot = Refl

instance (IProp' f, IProp' g) => IProp' (f :+: g) where
  type INot (f :+: g) = INot f :&: INot g
  icontradict s (IWith f) = s & \case
    L1 g -> icontradict g (f L)
    R1 g -> icontradict g (f R)
  inot = Refl

newtype (:⅋:) (a :: i -> Type) (b :: i -> Type) (x :: i) =
  IPar (forall (c :: Type). Y (INot b x %1 -> a x) (INot a x %1 -> b x) c -> c)

instance (IProp' f, IProp' g) => Prop' ((f :*: g) a) where
  type Not ((f :*: g) a) = (INot f :⅋: INot g) a
  (f :*: g) != IPar h = icontradict g (h R f)

instance (IProp' f, IProp' g) => Prop' ((f :⅋: g) a) where
  type Not ((f :⅋: g) a) = (INot f :*: INot g) a
  IPar h != (f :*: g) = icontradict (h R f) g

instance (IProp' f, IProp' g) => IProp' (f :*: g) where
  type INot (f :*: g) = INot f :⅋: INot g
  icontradict (f :*: g) (IPar h) = icontradict g (h R f)
  inot = Refl

instance (IProp' f, IProp' g) => IProp' (f :⅋: g) where
  type INot (f :⅋: g) = INot f :*: INot g
  icontradict (IPar h) (f :*: g) = icontradict (h R f) g
  inot = Refl

-- | Intuitionistic implication.
--
-- This is encoded as @Ur a ⊸ b@, i.e. a non-linear assumption in a
-- linear codomain.
newtype a ⊃ b = Imp
  (forall c. (Prop' a, Prop' b) => Y (Not b %1 -> WhyNot (Not a)) (a -> b) c -> c)

infixr 0 ⊃

imp :: (forall c. (Prop' a, Prop' b) => Y (Not b %1 -> WhyNot (Not a)) (a -> b) c -> c) %1 -> a ⊃ b
imp = Imp

runImp :: (Prop' a, Prop' b) => (a ⊃ b) %1 -> Y (Not b %1 -> WhyNot (Not a)) (a -> b) c -> c
runImp (Imp f) = f

impR' :: (Prop' a, Prop' b) => (a ⊃ b) %1 -> a -> b
impR' f = runImp f R

impL' :: (Prop' a, Prop' b) => (a ⊃ b) %1 -> Not b %1 -> WhyNot (Not a)
impL' f = runImp f L

data Noimp b a where
  Noimp :: a -> Not b %1 -> Noimp b a

instance (Prop' a, Prop' b) => Prop' (a ⊃ b) where
  type Not (a ⊃ b) = Noimp b a
  f != Noimp a b = runImp f R a != b

instance (Prop' a, Prop' b) => Prop' (Noimp b a) where
  type Not (Noimp b a) = a ⊃ b
  Noimp a b != f = runImp f R a != b

-- FTensor would match hkd. DFoo would match dependent-sum, dependent-hashmap. change hkd?
-- we need some way to talk about a partitioning/swizzling of a list into two lists
-- then you can project out subsets of the rows with a swizzle. then this generalizes to 'f's
-- that can be swizzled into 'g's and 'h's?
-- newtype DTensor :: [i] -> (i -> Type) -> Type
-- newtype DPar :: [i] -> (i -> Type) -> Type
--  ⊸ ⅋
--newtype a ⇀ b = Partial (a ⊸ WhyNot b)
-- a ⇀ b = Not a ⅋ WhyNot b = WhyNot b ⅋ Not a = Not (WhyNot b) ⊸ Not a = Ur b ⊸ Not a = b ⊃ Not a
