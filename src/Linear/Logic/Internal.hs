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

-- not is merely involutive. used to avoid passing dictionaries when they aren't used
type Prep a = Not (Not a) ~ a

class (Prop (Not a), Prep a) => Prop (a :: TYPE k) where
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
  x != Bot b = b (Top x)
  {-# inline (!=) #-}

-- | The unit for additive disjunction, \(\texttt{Void}\)
--
-- \(\texttt{Void}^\bot\) ≡ \(\top\)
instance Prop Void where
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
instance Prop Top where
  type Not Top = Void
  Top a != v = \case{} v a
  {-# inline (!=) #-}

-- | The unit for multiplicative disjunction, \(\bot\)
--
-- \(\bot^\bot\) ≡ \(\texttt{()}\)
instance Prop Bot where
  type Not Bot = ()
  Bot a != x = a (Top x)
  {-# inline (!=) #-}

{-
-- | Used to request a given side from 'With' or 'Par'.
--
-- An unlifted version of this is suplied by Linear.Logic.Y
type role Y nominal nominal nominal
type Y :: i -> j -> k -> Type
data Y a b c where
  L :: Y a b a
  R :: Y a b b
-}

-- With can be runtime rep polymorphic
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

instance (Prop a, Prop b) => Prop (a & b) where
  type Not (a & b) = Not a + Not b
  w != Left a = withL' w != a
  w != Right b = withR' w != b
  {-# inline (!=) #-}

infixr 2 +
type (+) = Either

instance (Prop a, Prop b) => Prop (Either a b) where
  type Not (Either a b) = Not a & Not b
  Left a != w = a != withL' w
  Right a != w = a != withR' w
  {-# inline (!=) #-}

infixr 3 *
type (*) = (,)

infixr 2 ⅋
type (⅋) :: forall i j. TYPE i -> TYPE j -> Type
type role (⅋) nominal nominal
-- | \(\par\) is multiplicative disjunction.
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

instance (Prep a, Prop b) => Prop (a * b) where
  type Not (a * b) = Not a ⅋ Not b
  (a, b) != p = parR' p a != b
  {-# inline (!=) #-}

instance (Prep a, Prop b) => Prop (a ⅋ b) where
  type Not (a ⅋ b) = Not a * Not b
  p != (a, b) = parR' p a != b
  {-# inline (!=) #-}

-- | This instance is for @(a %1 -> b)@ despite haddock's lies.
-- The injective type family on @Not@ forces me to use a flexible
-- instance, rather than have the instance self-improve
instance Prop b => Prop (a %m -> b) where
  type Not (a %m -> b) = Nofun m a b
  f != (Nofun a nb) = f a != nb
  {-# inline (!=) #-}

-- | The refutations of a linear haskell arrow are the same as the refutation of ⊸.
data Nofun m a b where
  Nofun :: a %m -> Not b %1 -> Nofun m a b

deriving stock instance (Show a, Show (Not b)) => Show (Nofun m a b)
deriving stock instance (Read a, Read (Not b)) => Read (Nofun m a b)
-- deriving stock instance (Eq a, Eq (Not b)) => Eq (Nofun m a b)
-- deriving stock instance (Ord a, Ord (Not b)) => Ord (Nofun m a b)

instance Prop b => Prop (Nofun m a b) where
  type Not (Nofun m a b) = a %m -> b
  Nofun a nb != f = f a != nb
  {-# inline (!=) #-}

infixr 0 ⊸

type (%->) = FUN 'One

-- | \(\multimap\) could be defined in terms of \(⅋\), but then I couldn't hang instances off it.
--
-- type p ⊸ q = Not p ⅋ q
newtype a ⊸ b = Lol (forall c. Y (Not b %1 -> Not a) (a %1 -> b) c -> c)

data a -#> b where (:-#>) :: a %1 -> Not b %1 -> a -#> b
infixr 3 -#>, :-#>

newtype a ⧟ b = Iso (forall c. Y (b ⊸ a) (a ⊸ b) c -> c)
infixr 0 ⧟

runLol :: a ⊸ b %1 -> Y (Not b %1 -> Not a) (a %1 -> b) c -> c
runLol (Lol f) = f

runIso :: a ⧟ b %1 -> Y (b ⊸ a) (a ⊸ b) c -> c
runIso (Iso f) = f

-- | Sometimes linear haskell needs some help to infer that we really want linear usage
linear :: (a %1 -> b) %1 -> a %1 -> b
linear = id

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

data a # b
  = ApartL (Not a) b
  | ApartR a (Not b)

instance (Prop a, Prop b) => Prop (a ⧟ b) where
  type Not (a ⧟ b) = a # b
  Iso f != ApartR a nb = f R != (a :-#> nb)
  Iso f != ApartL na b = f L != (b :-#> na)

instance (Prop a, Prop b) => Prop (a # b) where
  type Not (a # b) = a ⧟ b
  ApartR a nb != Iso f = f R != (a :-#> nb)
  ApartL na b != Iso f = f L != (b :-#> na)

class Iso p where
  iso :: (forall c. Y (b ⊸ a) (a ⊸ b) c -> c) %1 -> p a b
  apart :: Not (p a b) %1 -> a # b

class Iso p => Lol p where
  lol :: (forall c. Y (Not b %1 -> Not a) (a %1 -> b) c -> c) %1 -> p a b
  apartR :: Not (p a b) %1 -> a -#> b

instance Iso (⧟) where
  iso = Iso
  apart = id

instance Iso (⊸) where
  iso f = f R
  apart (a :-#> nb) = ApartR a nb

instance Lol (⊸) where
  lol = Lol
  apartR x = x

instance Iso (FUN m) where
  iso f = \x -> fun' (f R) x
  apart (Nofun a nb) = ApartR a nb

instance Lol (FUN m) where
  lol f = \x -> f R x
  apartR (Nofun a nb) = a :-#> nb

instance (Prep a, Prop b) => Prop (a ⊸ b) where
  type Not (a ⊸ b) = a -#> b
  f != (a :-#> nb) = fun f a != nb

instance (Prep a, Prop b) => Prop (a -#> b) where
  type Not (a -#> b) = a ⊸ b
  (a :-#> nb) != f = fun f a != nb

deriving stock instance (Show a, Show (Not b)) => Show (a -#> b)
deriving stock instance (Read a, Read (Not b)) => Read (a -#> b)
-- deriving stock instance (Eq a, Eq (Not b)) => Eq (a # b)
-- deriving stock instance (Ord a, Ord (Not b)) => Ord (a # b)

{-
-- | Derive a linear function for the contrapositive from a
-- linear logic impliciation.
--
-- @
-- 'unfun' :: forall a b. 'Prop' a => (a '⊸' b) %1 -> a %1 -> b
-- @
unfun :: (a ⊸ b) %1 -> Not b %1 -> Not a
unfun (Lol f) = f L
{-# inline unfun #-}
-}

-- | Derive a linear function from a linear logic impliciation.
--
-- @
-- 'fun' :: forall a b. 'Prop' a => (a '⊸' b) %1 -> a %1 -> b
-- @
--
fun' :: (a ⊸ b) %1 -> (a %1 -> b)
fun' (Lol f) = lol f
{-# inline fun' #-}

fun :: (Lol l, Lol l') => l (a ⊸ b) (l' a b)
fun = lol \case
  L -> apartR
  R -> \(Lol f) -> lol f
{-# inline fun #-}

lolPar :: (Iso iso, Prep a) => (a ⊸ b) `iso` (Not a ⅋ b)
lolPar = iso \case
  L -> lol \case
    L -> \(a :-#> nb) -> (a, nb)
    R -> \(Par f) -> Lol f
  R -> lol \case
    L -> \(a, nb) -> a :-#> nb
    R -> \(Lol f) -> Par f

contra'' :: forall l p q. (Lol l, Prep p, Prep q) => p ⊸ q %1 -> l (Not q) (Not p)
contra'' = \(Lol f) -> lol \case
  L -> \na -> f R na
  R -> \nb -> f L nb

contra' :: forall l l' p q. (Lol l, Lol l', Prep p, Prep q) => l (p ⊸ q) (l' (Not q) (Not p))
contra' = lol \case
  L -> \nf -> apartR nf & \(p :-#> nq) -> nq :-#> p
  R -> contra''

contra :: forall iso p q. (Iso iso, Prep p, Prep q) => iso (p ⊸ q) (Not q ⊸ Not p)
contra = iso \case
  L -> contra'
  R -> contra'

contraIso'' :: forall iso p q. (Iso iso, Prep p, Prep q) => p ⧟ q %1 -> iso (Not q) (Not p)
contraIso'' = \(Iso f) -> iso \case
  L -> contra' (f L)
  R -> contra' (f R)

contraIso' :: forall l iso p q. (Lol l, Iso iso, Prep p, Prep q) => l (p ⧟ q) (iso (Not q) (Not p))
contraIso' = lol \case
  L -> \x -> apart x & \case
    ApartL p nq -> ApartL nq p
    ApartR p nq -> ApartR nq p
  R -> contraIso''

contraIso :: forall iso p q. (Iso iso, Prep p, Prep q) => iso (p ⧟ q) (Not q ⧟ Not p)
contraIso = iso \case
  L -> contraIso'
  R -> contraIso'

-- | The \(?a\) or "why not?" modality.
type role WhyNot nominal
newtype WhyNot a = WhyNot (forall r. Not a -> r)

whyNot :: (forall r. Not a -> r) %1 -> WhyNot a
whyNot = WhyNot

because :: WhyNot a %1 -> Not a -> r
because (WhyNot a) = a
{-# inline because #-}

-- | The exponential, or unrestricted modality, \( !a \)
--
-- This embeds arbitrary non-linear Haskell values into 'Prop'.
instance Prep a => Prop (Ur a) where
  type Not (Ur a) = WhyNot (Not a)
  Ur a != WhyNot f = f a
  {-# inline (!=) #-}

instance Prep a => Prop (WhyNot a) where
  type Not (WhyNot a) = Ur (Not a)
  WhyNot f != Ur a = f a
  {-# inline (!=) #-}

-- |
-- @
-- 'weakenUr' :: forall p q. 'Prop' p => p ⊸ 'Ur' q ⊸ p
-- @
weakenUr :: (Prop p, Lol l, Lol l') => l p (l' (Ur q) p)
weakenUr = lol \case
  L -> \x -> apartR x & \(Ur {} :-#> np) -> np
  R -> \p -> lol \case
    L -> \np -> p != np
    R -> \Ur{} -> p
{-# inline weakenUr #-}

apUr :: forall p q. (Prep p, Prep q) => Ur (p ⊸ q) ⊸ Ur p ⊸ Ur q
apUr = lol \case
  L -> \(Ur p :-#> WhyNot nq) -> whyNot \nppq -> nq (fun nppq p)
  R -> \(Ur nppq) -> lol \case
    L -> \(WhyNot nq) -> whyNot \p -> nq (fun nppq p)
    R -> \(Ur p) -> Ur (fun nppq p)
{-# inline apUr #-}

extractUr :: (Lol l, Prop p) => l (Ur p) p
extractUr = lol \case
  L -> \np -> whyNot \p -> p != np
  R -> \(Ur p) -> p
{-# inline extractUr #-}

duplicateUr :: Lol l => l (Ur p) (Ur (Ur p))
duplicateUr = lol \case
  L -> \(WhyNot f) -> WhyNot \p -> f (Ur p)
  R -> \(Ur p) -> Ur (Ur p)
{-# inline duplicateUr #-}

dupUr :: (Iso i, Prop a) => i (Ur a) (Ur a * Ur a)
dupUr = iso \case
  L -> lol \case
    L -> \n -> par \case
      L -> (n !=)
      R -> (n !=)
    R -> \(Ur a, Ur{}) -> (Ur a)
  R -> lol \case
    L -> \p -> WhyNot \a -> because (parR' p (Ur a)) a
    R -> \(Ur a) -> (Ur a, Ur a)

contractUr :: (Prep p, Prop q) => (Ur p ⊸ Ur p ⊸ q) ⊸ Ur p ⊸ q
contractUr = lol \case
  L -> \(Ur p :-#> nq) -> (Ur p :-#> (Ur p :-#> nq))
  R -> \x -> lol \case
    L -> \nq -> whyNot \p -> contra' (fun x (Ur p)) nq != Ur p
    R -> \(Ur p) -> fun (fun x (Ur p)) (Ur p)
{-# inline contractUr #-}

returnWhyNot :: (Lol l, Prop p) => l p (WhyNot p)
returnWhyNot = contra' extractUr
{-# inline returnWhyNot #-}

joinWhyNot :: (Lol l, Prep p) => l (WhyNot (WhyNot p)) (WhyNot p)
joinWhyNot = contra' duplicateUr
{-# inline joinWhyNot #-}

withL :: Lol l => l (a & b) a
withL = lol \case
  L -> Left
  R -> withL'

withR :: Lol l => l (a & b) b
withR = lol \case
  L -> Right
  R -> withR'

left :: Lol l => l a (a + b)
left = lol \case
  L -> withL'
  R -> Left

right :: Lol l => l b (a + b)
right = lol \case
  L -> withR'
  R -> Right

parR :: (Lol l, Lol l', Prep a) => l (a ⅋ b) (l' (Not a) b)
parR = lol \case
  L -> \g -> apartR g & \(x :-#> y) -> (x, y)
  R -> \p -> lol \case
    L -> parL' p
    R -> parR' p

parL :: (Lol l, Lol l', Prep b) => l (a ⅋ b) (l' (Not b) a)
parL = lol \case
  L -> \g -> apartR g & \(x :-#> y) -> (y, x)
  R -> \p -> lol \case
    L -> parR' p
    R -> parL' p



newtype DWith f g = DWith (forall x. f x %1 -> g x)

dwith :: (forall x. f x %1 -> g x) %1 -> DWith f g
dwith = DWith

runDWith :: DWith f g %1 -> f x %1 -> g x
runDWith (DWith f) = f

type IPrep f = INot (INot f) ~ f

class
  ( IProp (INot f)
  , IPrep f
  , forall a. Prop (f a)
  ) => IProp (f :: i -> Type) where
  type INot (f :: i -> Type) = (c :: i -> Type) | c -> f
  icontradict :: f a %1 -> INot f a %1 -> r
  inot :: INot f a :~: Not (f a)

instance Prop a => IProp (Const a) where
  type INot (Const a) = Const (Not a)
  inot = Refl
  icontradict (Const a) (Const na) = a != na

instance Prop a => Prop (Const a b) where
  type Not (Const a b) = Const (Not a) b
  Const a != Const na = a != na

instance IProp g => Prop (DWith f g) where
  type Not (DWith f g) = DSum f (INot g)
  h != (f :=> g) = icontradict g (runDWith h f)

instance IProp g => Prop (DSum f g) where
  type Not (DSum f g) = DWith f (INot g)
  (f :=> g) != h = icontradict g (runDWith h f)

type (:&:) :: forall i. (i -> Type) -> (i -> Type) -> i -> Type
newtype (:&:) f g a = IWith (forall h. Y f g h -> h a)

instance (IProp f, IProp g) => Prop ((:&:) f g a) where
  type Not ((:&:) f g a) = (INot f :+: INot g) a
  (!=) (IWith f) = \case
    L1 g -> icontradict (f L) g
    R1 g -> icontradict (f R) g

instance (IProp f, IProp g) => Prop ((:+:) f g a) where
  type Not ((:+:) f g a) = (INot f :&: INot g) a
  L1 g != IWith f = icontradict g (f L)
  R1 g != IWith f = icontradict g (f R)

instance (IProp f, IProp g) => IProp (f :&: g) where
  type INot (f :&: g) = INot f :+: INot g
  icontradict (IWith f) = \case
    L1 g -> icontradict (f L) g
    R1 g -> icontradict (f R) g
  inot = Refl

instance (IProp f, IProp g) => IProp (f :+: g) where
  type INot (f :+: g) = INot f :&: INot g
  icontradict s (IWith f) = s & \case
    L1 g -> icontradict g (f L)
    R1 g -> icontradict g (f R)
  inot = Refl

newtype (:⅋:) (a :: i -> Type) (b :: i -> Type) (x :: i) =
  IPar (forall (c :: Type). Y (INot b x %1 -> a x) (INot a x %1 -> b x) c -> c)

instance (IProp f, IProp g) => Prop ((f :*: g) a) where
  type Not ((f :*: g) a) = (INot f :⅋: INot g) a
  (f :*: g) != IPar h = icontradict (h R f) g

instance (IProp f, IProp g) => Prop ((f :⅋: g) a) where
  type Not ((f :⅋: g) a) = (INot f :*: INot g) a
  IPar h != (f :*: g) = icontradict (h R f) g

instance (IProp f, IProp g) => IProp (f :*: g) where
  type INot (f :*: g) = INot f :⅋: INot g
  icontradict (f :*: g) (IPar h) = icontradict (h R f) g
  inot = Refl

instance (IProp f, IProp g) => IProp (f :⅋: g) where
  type INot (f :⅋: g) = INot f :*: INot g
  icontradict (IPar h) (f :*: g) = icontradict (h R f) g
  inot = Refl

-- FTensor would match hkd. DFoo would match dependent-sum, dependent-hashmap. change hkd?
-- we need some way to talk about a partitioning/swizzling of a list into two lists
-- then you can project out subsets of the rows with a swizzle. then this generalizes to 'f's
-- that can be swizzled into 'g's and 'h's?
-- newtype DTensor :: [i] -> (i -> Type) -> Type
-- newtype DPar :: [i] -> (i -> Type) -> Type


--------------------------------------------------------------------------------
-- Interplay between connectives that needs weakening
--------------------------------------------------------------------------------

tensorToWith
  :: (Lol l, Prop p, Consumable p, Prop q, Consumable q)
  => l (p * q) (p & q)
tensorToWith = lol \case
  L -> \case
    Left np -> par \case
      L -> \q -> lseq q np
      R -> \p -> p != np
    Right nq -> par \case
      L -> \q -> q != nq
      R -> \p -> lseq p nq
  R -> \(p, q) -> with \case
    L -> lseq q p
    R -> lseq p q

eitherToPar
  :: (Lol l, Consumable p, Consumable q, Prop p, Prop q)
  => l (Not p + Not q) (Not p ⅋ Not q)
eitherToPar = contra' tensorToWith

--------------------------------------------------------------------------------
-- Excluded middle and decidability
--------------------------------------------------------------------------------

-- | multiplicative excluded-middle, equivalent to multiplicative law of non-contradiction
mem :: Prep p => p ⅋ Not p
mem = par \case L -> \x -> x; R -> \x -> x

-- | additive excluded middle, or additive law of non-contradiction is a property of a proposition
-- not a law.
type Decidable p = p + Not p

--------------------------------------------------------------------------------
-- Ur is a Seely comonad
--------------------------------------------------------------------------------

seely'' :: Ur (p & q) %1 -> Ur p * Ur q
seely'' = \(Ur pwq) -> (Ur (withL pwq), Ur (withR pwq))

unseely'' :: (Ur p * Ur q) %1 -> Ur (p & q)
unseely'' = \(Ur p, Ur q) -> Ur (with \case L -> p; R -> q)

contraseely'' :: WhyNot p ⅋ WhyNot q %1 -> WhyNot (p + q)
contraseely'' = \r -> WhyNot \pwq -> because (parL' r (Ur (withR pwq))) (withL pwq)

contraunseely'' :: WhyNot (p + q) %1 -> WhyNot p ⅋ WhyNot q
contraunseely'' = \n -> par \case
  L -> \(Ur q) -> WhyNot \p -> because n (with \case L -> p; R -> q)
  R -> \(Ur p) -> WhyNot \q -> because n (with \case L -> p; R -> q)

seely' :: Lol l => l (Ur (p & q)) (Ur p * Ur q)
seely' = lol \case L -> contraseely''; R -> seely''

unseely' :: Lol l => l (Ur p * Ur q) (Ur (p & q))
unseely' = lol \case L -> contraunseely''; R -> unseely''

-- contraseely' :: Lol l => l (WhyNot p ⅋ WhyNot q) (WhyNot (p + q))
-- contraseely' = lol \case L -> seely''; R -> contraseely''

-- contraunseely' :: Lol l => l (WhyNot (p + q)) (WhyNot p ⅋ WhyNot q)
-- contraunseely' = lol \case L -> unseely''; R -> contraunseely''

-- | \(!\) is a <https://ncatlab.org/nlab/files/SeelyLinearLogic.pdf Seely comonad>
--
-- A seely comonad is a strong monoidal functor from cartesian monoidal structure to
-- symmetric monoidal structure.
seely :: Iso i => i (Ur (p & q)) (Ur p * Ur q)
seely = iso \case L -> unseely'; R -> seely'

-- contraseely :: Iso i => i (WhyNot p ⅋ WhyNot q) (WhyNot (p + q))
-- contraseely = iso \case L -> contraunseely'; R -> contraseely'

seelyTop'' :: Ur Top %1 -> ()
seelyTop'' = consume

contraunseelyTop'' :: WhyNot Void %1 -> Bot
contraunseelyTop'' = \n -> because n (Top ())

contraseelyTop'' :: Bot %1 -> WhyNot Void
contraseelyTop'' = \(Bot f) -> WhyNot \top -> f top

unseelyTop'' :: () %1 -> Ur Top
unseelyTop'' = \() -> Ur (Top ())

seelyTop :: Iso iso => iso (Ur Top) ()
seelyTop = iso \case
  L -> lol \case
    L -> contraunseelyTop''
    R -> unseelyTop''
  R -> lol \case
    L -> contraseelyTop''
    R -> seelyTop''

-- | valid in a semicartesian *-autonomous lattice
--
-- This is generally not valid in linear logic, but holds
-- in affine logic, and seems to hold here.
semiseely :: (Iso i, Prep p) => i (Ur (p * q)) (Ur p * Ur q)
semiseely = iso \case
  L -> lol \case
    L -> \k -> par \case
      L -> \(Ur q) -> WhyNot \p -> because k (p, q)
      R -> \(Ur p) -> WhyNot \q -> because k (p, q)
    R -> \(Ur p, Ur q) -> Ur (p, q)
  R -> lol \case
    L -> \x -> WhyNot \(p,q) -> because (parR' x (Ur p)) q
    R -> \(Ur (p, q)) -> (Ur p, Ur q)

semiseelyUnit :: Iso i => i (Ur ()) ()
semiseelyUnit = iso \case
  L -> lol \case
    L -> \n -> because n ()
    R -> \() -> Ur ()
  R -> lol \case
    L -> \b -> WhyNot \p -> b != p
    R -> \(Ur ()) -> ()

{- nonsense
type a -&> b = Not a ⊸ b

curryWith'' :: Lol l => (a & b ⊸ c) %1 -> l a (b -&> c)
curryWith'' f = lol \case
  R -> \a -> lol \case 
    R -> \nb -> _ (fun f) a nb
  L -> _ f
-}

