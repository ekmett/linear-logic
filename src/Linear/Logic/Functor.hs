{-# language CPP #-}
{-# language BlockArguments #-}
{-# language DefaultSignatures #-}
{-# language DerivingStrategies #-}
{-# language EmptyCase #-}
{-# language ExplicitNamespaces #-}
{-# language ImportQualifiedPost #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies #-}
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
{-# language ImportQualifiedPost #-}
{-# language Trustworthy #-}



-- {-# options_ghc -Wno-unused-imports #-}

module Linear.Logic.Functor where

import Data.Type.Equality
import Data.Void
import Data.Kind
import GHC.Types
import Linear.Logic.Internal
import Linear.Logic.Y
import Prelude.Linear hiding (id,(.),flip)

type family NotApart (p :: Type -> Type -> Type) :: Type -> Type -> Type

class 
  ( forall a b. (Prop a, Prop b) => Prop (p a b)
  , NotApart (NotIso p) ~ p
  ) => Iso p where
  type NotIso p = (q :: Type -> Type -> Type) | q -> p
  iso :: (forall c. Y (b ⊸ a) (a ⊸ b) c -> c) %1 -> p a b
  apart :: Not (p a b) %1 -> b # a
  notIso :: NotIso p b a :~: Not (p a b)
  notApart :: NotApart (NotIso p) a b :~: p a b

class (Iso p, Profunctor p) => Lol (p :: Type -> Type -> Type) where
  lol :: (forall c. Y (Not b %1 -> Not a) (a %1 -> b) c -> c) %1 -> p a b
  apartR :: Not (p a b) %1 -> b <#- a

type instance NotApart (#) = (⧟)
instance Iso (⧟) where
  type NotIso (⧟) = (#)
  iso = Iso
  apart = \x -> x
  notIso = Refl
  notApart = Refl

type instance NotApart (<#-) = (⊸)
instance Iso (⊸) where
  type NotIso (⊸) = (<#-) 
  iso f = f R
  apart (a :-#> nb) = ApartR a nb
  notIso = Refl
  notApart = Refl

type instance NotApart Noimp = (⊃)
instance Iso (⊃) where
  type NotIso (⊃) = Noimp
  iso f = Imp \case
    R -> fun (f R)
    L -> \nb -> whyNot \a -> a != runLol (f R) L nb
  apart (Noimp a nb) = ApartR a nb
  notIso = Refl
  notApart = Refl

instance Lol (⊸) where
  lol = Lol
  apartR x = x

type instance NotApart (Nofun m) = FUN m

instance Iso (FUN m) where
  type NotIso (FUN m) = Nofun m
  iso f = \x -> fun' (f R) x
  apart (Nofun a nb) = ApartR a nb
  notIso = Refl
  notApart = Refl


instance Lol (FUN m) where
  lol f = \x -> linear (f R) x
  apartR (Nofun a nb) = a :-#> nb

instance Lol (⊃) where
  lol f = Imp \case
    R -> \x -> linear (f R) x
    L -> \nb -> whyNot \a -> a != f L nb
  apartR (Noimp a nb) = a :-#> nb

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

funIso :: (Lol l, Iso i) => l (a ⧟ b) (i a b)
funIso = lol \case
  L -> apart
  R -> \(Iso f) -> iso f

class Category p where
  id :: Prop a => p a a
  (.) :: (Prop a, Prop b, Prop c) => p b c %1 -> p a b %1 -> p a c

instance Category (FUN 'One) where
  id x = x
  f . g = \x -> f (g x)

-- | Here we have the ability to provide more refutations, because we can walk
-- all the way back to my arrows. This is internal to my logic.
class (forall a b. (Prop a, Prop b) => Prop (p a b)) => NiceCategory p where
  o :: (Lol l, Lol l', Prop a, Prop b, Prop c) => l (p b c) (l' (p a b) (p a c))

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
    L -> \nf -> apartR nf & \case
      iab :-#> ApartL na c -> ApartL (runLol (runIso iab L) L na) c
      iab :-#> ApartR a nc -> ApartR (runLol (runIso iab R) R a) nc
    R -> \bc -> lol \case
      L -> \case
        ApartL na c -> ApartL na (runLol (runIso bc L) R c)
        ApartR a nc -> ApartR a (runLol (runIso bc R) L nc)
      R -> (bc .)

class
  ( forall a. Prop a => Prop (f a)
  ) => Functor f where
  fmap' :: (Prop a, Prop b, Lol l, Lol l') => l (Ur (a ⊸ b)) (l' (f a) (f b))

fmap :: forall f a b l. (Functor f, Prop a, Prop b, Lol l) => (a ⊸ b) -> l (f a) (f b)
fmap  f = fmap' (Ur f)

fmapIso' :: (Functor f, Prop a, Prop b, Lol l, Iso i) => l (Ur (a ⧟ b)) (i (f a) (f b))
fmapIso' = lol \case
  L -> \ni -> apart ni & \case
    ApartL nfa fb -> whyNot \a2b -> fmap (inv' a2b) fb != nfa
    ApartR fa nfb -> whyNot \a2b -> fmap (funIso a2b) fa != nfb
  R -> \(Ur a2b) -> iso \case
    L -> fmap (inv' a2b)
    R -> fmap (funIso a2b)

fmapIso :: (Functor f, Prop a, Prop b, Iso i) => (a ⧟ b) -> i (f a) (f b)
fmapIso f = fmapIso' (Ur f)

instance Functor (FUN m a) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \(a2b :-#> Nofun a nc) -> WhyNot \c2b -> a2b a != runLol c2b L nc
    R -> \(Ur xb) -> lol \case
      L -> linear \(Nofun a nb) -> Nofun a (runLol xb L nb)
      R -> \a2x a -> fun' xb (a2x a)

instance Prop x => Functor ((⊃) x) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \(xia :-#> Noimp x nb) ->
      WhyNot \a2b -> fun' a2b (runImp xia R x) != nb
    R -> \(Ur a2b) -> lol \case
      L -> linear \(Noimp x nb) -> Noimp x (contra' a2b nb)
      R -> \xia -> imp \case
        L -> linear \nb -> WhyNot \x -> runLol a2b R (impR' xia x) != nb
        R -> \x -> fun' a2b (impR' xia x)

instance Prop x => Functor ((,) x) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \((x,a) :-#> nxpnb) ->
      WhyNot \a2b -> x != parL' nxpnb (fun' a2b a)
    R -> \(Ur f) -> lol \case
      L -> \nxpnb -> par \case
        L -> \a -> parL' nxpnb (fun' f a)
        R -> \x -> contra' f (parR' nxpnb x)
      R -> \(x, a) -> (x, fun' f a)

instance Prop x => Functor ((⊸) x) where
  -- fmap' = fun (dimap lolPar (inv' lolPar) . fmap')
  fmap' = lol \case
    L -> \nf -> apartR nf & \(x2a :-#> x :-#> nb) ->
      WhyNot \a2b -> fun' a2b (fun' x2a x) != nb
    R -> \(Ur f) -> lol \case
      L -> \x -> x & \(a :-#> nb) -> a :-#> contra' f nb
      R -> linear \g -> lol \case
        L -> linear \nb -> contra' g (contra' f nb)
        R -> \a -> fun' f (fun' g a)

class Functor f => MFunctor f where
  mfmap :: (Prop a, Prop b, Lol l, Lol l') =>  l (a ⊸ b) (l' (f a) (f b))

mfmapTensor' :: (Prop x, Prop a, Prop b, Lol l) => (a ⊸ b) %1 -> l (x, a) (x, b)
mfmapTensor' = \a2b -> lol \case
  L -> \nxpnb -> par \case
    L -> \a -> parL' nxpnb (fun' a2b a)
    R -> \x -> contra' a2b (parR' nxpnb x)
  R -> \(x,a) -> (x, fun' a2b a)

mfmapIso :: (MFunctor f, Prop a, Prop b, Lol l, Iso i) => l (a ⧟ b) (i (f a) (f b))
mfmapIso = lol \case
  L -> \ni -> apart ni & \case
    ApartR fa nfb -> apart (contra' mfmap (fa :-#> nfb))
    ApartL nfa fb -> swap $ apart (contra' mfmap (fb :-#> nfa))
  R -> \a2b -> iso \case
    L -> mfmap (runIso a2b L)
    R -> mfmap (runIso a2b R)

instance Prop x => MFunctor ((,) x) where
  mfmap = lol \case
    L -> \nf -> apartR nf & \((x,a) :-#> nxpnb) ->
      a :-#> (parR' nxpnb x)
    R -> mfmapTensor'

instance Prop x => MFunctor ((⅋) x) where
  mfmap = lol \case
    L -> \nf -> apartR nf & \(xpa :-#> (nx, nb)) ->
      parR xpa nx :-#> nb
    R -> contra' . mfmapTensor' . contra'

-- lolPar :: (Iso iso, Prep a) => (a ⊸ b) `iso` (Not a ⅋ b)

instance Prop x => MFunctor ((⊸) x) where
  mfmap = lol \case
    L -> \nf -> apartR nf & \(x2a :-#> x :-#> nb) -> fun' x2a x :-#> nb
    R -> \a2b -> lol \case
      L -> \(x :-#> nb) -> x :-#> contra' a2b nb
      R -> (a2b .)

instance MFunctor (FUN 'One x) where
  mfmap = lol \case
    L -> \nf -> apartR nf & \(x2a :-#> Nofun x nb) -> x2a x :-#> nb
    R -> \(a2b :: a ⊸ b) -> lol \case
      L -> linear \(Nofun x nb) -> Nofun x (contra' a2b nb)
      R -> \x2a x -> fun' a2b (x2a x)

instance Functor Ur where
  fmap' = lol \case
    L -> \nf -> apartR nf & \(Ur a :-#> f) ->
      WhyNot \p -> because f (fun' p a)
    R -> \(Ur f) -> lol \case
      L -> \(WhyNot cb) -> WhyNot \a -> cb (fun f a)
      R -> \(Ur a) -> Ur (fun f a)

instance Functor WhyNot where
  fmap' = lol \case
    L -> \nf -> apartR nf & \case
      wna :-#> Ur nb ->
        whyNot \a2b -> because wna (contra' a2b nb)
    R -> \(Ur f) -> lol \case
      L -> \(Ur nb) -> Ur (contra' f nb)
      R -> \na2v -> whyNot \nb -> because na2v (contra' f nb)

instance Prop a => Functor (Either a) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \case
      Left a :-#> g -> whyNot \_ -> a != withL g
      Right b :-#> g -> whyNot \p -> fun' p b != withR g
    R -> \(Ur f) -> lol \case
      L -> \nawnb -> with \case
        L -> withL nawnb
        R -> contra' f (withR nawnb)
      R -> \case
        Left a -> Left a
        Right x -> Right (fun f x)

instance Prop p => Functor ((&) p) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \case
      pwa :-#> Left np -> whyNot \_ -> withL' pwa != np
      pwa :-#> Right nb -> whyNot \a2b -> fun' a2b (withR' pwa) != nb
    R -> \(Ur f) -> lol \case
      L -> \case
        Left np -> Left np
        Right nb -> Right (contra' f nb)
      R -> \pwa -> with \case
        L -> withL' pwa
        R -> fun' f (withR' pwa)

instance Prop a => Functor ((⅋) a) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \case
      apc :-#> (na,nb) ->
        WhyNot \c2b -> parR' apc na != contra' c2b nb
    R -> \(Ur f) -> lol \case
      L -> \(na,nb) -> (na, contra' f nb)
      R -> \apa1 -> par \case
        L -> \nb -> parL' apa1 (contra' f nb)
        R -> \na -> fun' f (parR' apa1 na)

class (Functor f, Functor g) => Adjunction f g | f -> g, g -> f where
  adj :: (Iso iso, Prop a, Prop b) => iso (f a ⊸ b) (a ⊸ g b)

instance Prop e => Adjunction ((,) e) ((⊸) e) where
  adj = iso \case
    L -> uncurryTensor' . flip
    R -> flip . curryTensor'

-- | The directed apartness as the left adjoint of (⅋) e. Found in 
-- <https://www.math.mcgill.ca/rags/nets/fill.pdf>.
instance Prop e => Adjunction ((<#-) e) ((⅋) e) where
  adj = iso \case
    L -> lol \case
      L -> \case
        (a :-#> ne) :-#> nb -> a :-#> (ne, nb)
      R -> \a2epb -> lol \case
        L -> \nb -> lol \case
          L -> \ne -> contra' a2epb (ne, nb)
          R -> \a -> parL' (fun' a2epb a) nb
        R -> \(a :-#> ne) -> parR' (fun' a2epb a) ne
    R -> lol \case
      L -> \(a :-#> (ne, nb)) -> (a :-#> ne) :-#> nb
      R -> \k -> lol \case
        L -> \(ne, nb) -> contra' (contra' k nb) ne
        R -> \a -> par \case
          L -> linear \nb -> fun' (contra' k nb) a
          R -> \ne -> fun' k (a :-#> ne)

instance Prop b => Functor ((<#-) b) where
  fmap' = lol \case
    L -> \nk -> apartR nk & \case
      (a :-#> nb) :-#> c2b ->
        WhyNot \a2c -> fun' c2b (fun' a2c a) != nb
    R -> \(Ur a2c) -> lol \case
      L -> \c2b -> c2b . a2c
      R -> linear \(a :-#> nb) -> fun' a2c a :-#> nb

class
  ( forall a. Prop a => Prop (f a)
  ) => Contravariant f where
  contramap' :: (Prop a, Prop b, Lol l, Lol l') => l (Ur (a ⊸ b)) (l' (f b) (f a))


contramap :: (Contravariant f, Prop a, Prop b, Lol l) => (a ⊸ b) -> l (f b) (f a)
contramap f = contramap' (Ur f)

class
  ( forall a. Prop a => Functor (t a)
  ) => Profunctor t where
  dimap'
    :: (Prop a, Prop b, Prop c, Prop d, Lol l, Lol l', Lol l'')
    => l (Ur (a ⊸ b)) (l' (Ur (c ⊸ d)) (l'' (t b c) (t a d)))

dimap
  :: (Profunctor t, Prop a, Prop b, Prop c, Prop d, Lol l)
  => (a ⊸ b) -> (c ⊸ d) -> l (t b c) (t a d)
dimap f g = dimap' (Ur f) (Ur g)

dimapIso'
  :: (Profunctor t, Prop a, Prop b, Prop c, Prop d, Lol l, Lol l', Iso i)
  => l (Ur (a ⧟ b)) (l' (Ur (c ⧟ d)) (i (t b c) (t a d)))
dimapIso' = lol \case
  L -> \ni -> apartR ni & \(Ur cd :-#> tbc2tad) -> apart tbc2tad & \case
    ApartL ntbc tad -> whyNot \ab -> dimap (runIso ab L) (runIso cd L) tad != ntbc
    ApartR tbc ntad -> whyNot \ab -> dimap (runIso ab R) (runIso cd R) tbc != ntad
  R -> \(Ur ab) -> lol \case
    L -> \nj -> apart nj & \case
      ApartL ntbc tad -> whyNot \cd -> dimap (runIso ab L) (runIso cd L) tad != ntbc
      ApartR tbc ntad -> whyNot \cd -> dimap (runIso ab R) (runIso cd R) tbc != ntad
    R -> \(Ur cd) -> iso \case
      -- improve the type of Y used by iso so we can refine this to a single def?
      L -> dimap (runIso ab L) (runIso cd L)
      R -> dimap (runIso ab R) (runIso cd R)

dimapIso
  :: (Profunctor t, Prop a, Prop b, Prop c, Prop d, Iso i)
  => (a ⧟ b) -> (c ⧟ d) -> i (t b c) (t a d)
dimapIso f g = dimapIso' (Ur f) (Ur g)

instance Profunctor (⊸) where
  dimap' = lol \case
    L -> \nf -> apartR nf & \case
      Ur c2d :-#> nh -> apartR nh & \(b2c :-#> a :-#> nd) ->
        WhyNot \a2b -> fun' c2d (fun' b2c (fun' a2b a)) != nd
    R -> \(Ur f) -> lol \case
      L -> \ng -> apartR ng & \(b2c :-#> a :-#> nd) ->
         WhyNot \c2d -> fun' c2d (fun' b2c (fun' f a)) != nd
      R -> \(Ur g) -> lol \case
        L -> linear \(a :-#> nd) -> fun' f a :-#> contra' g nd
        R -> linear \h -> g . h . f

instance Profunctor (<#-) where
  dimap' = lol \case
    L -> \ni -> apartR ni & \((Ur c2d) :-#> nj) -> 
      apartR nj & \((c :-#> nb) :-#> d2a) -> 
        WhyNot \a2b -> fun' a2b (fun' d2a (fun' c2d c)) != nb
    R -> \(Ur a2b) -> lol \case
      L -> \ni -> apartR ni & \((c :-#> nb) :-#> d2a) -> 
        WhyNot \c2d -> fun' a2b (fun' d2a (fun' c2d c)) != nb
      R -> \(Ur c2d) -> lol \case
        L -> \d2a -> lol \case
          L -> linear \nb -> contra' c2d (contra' d2a (contra' a2b nb))
          R -> \c -> fun' a2b (fun' d2a (fun' c2d c))
        R -> linear \(c :-#> nb) -> fun' c2d c :-#> contra' a2b nb

instance Prop y => Functor (Noimp y) where
  fmap' = lol \case
    L -> \ni -> apartR ni & \case
      Noimp a ny :-#> b2y -> 
        WhyNot \a2b -> impR' b2y (fun' a2b a) != ny
    R -> \(Ur a2b) -> lol \case
      L -> \biy -> imp \case 
        L -> \ny -> contra' (fmap a2b) (impL' biy ny)
        R -> \a -> impR' biy (fun' a2b a)
      R -> \(Noimp a ny) -> Noimp (fun' a2b a) ny

instance Prop y => Functor (Nofun m y) where
  fmap' = lol \case
    L -> \ni -> apartR ni & \case
      Nofun a ny :-#> b2y -> WhyNot \a2b -> b2y (fun' a2b a) != ny
    R -> \(Ur (a2b :: a ⊸ b)) -> lol \case
      L -> \(b2y :: b %m -> y) a -> b2y (fun' a2b a)
      R -> linear \(Nofun a ny :: Nofun m y a) -> Nofun (fun' a2b a) ny

instance Profunctor Noimp where
  dimap' = lol \case
    L -> \ni -> apartR ni & \case
      Ur c2d :-#> nj -> apartR nj & \case
        Noimp c nb :-#> d2a -> WhyNot \a2b -> fun' a2b (impR' d2a (fun' c2d c)) != nb
    R -> \(Ur a2b) -> lol \case
      L -> \nj -> apartR nj & \case
        Noimp c nb :-#> d2a -> WhyNot \c2d -> fun' a2b (impR' d2a (fun' c2d c)) != nb
      R -> \(Ur c2d) -> lol \case 
        L -> linear \dia -> imp \case
          L -> \nb -> WhyNot \c -> dia != Noimp (fun' c2d c) (contra' a2b nb)
          R -> \c -> fun' a2b (impR' dia (fun' c2d c))
        R -> linear \(Noimp c nb) -> Noimp (fun' c2d c) (contra' a2b nb)

instance Profunctor (Nofun m) where
  dimap' = lol \case
    L -> \ni -> apartR ni & \case
      Ur c2d :-#> nj -> apartR nj & \case
        Nofun c nb :-#> d2a -> WhyNot \a2b -> fun' a2b (d2a (fun' c2d c)) != nb
    R -> \(Ur (a2b :: a ⊸ b)) -> lol \case
      L -> \ni -> apartR ni & \case
        Nofun c nb :-#> d2a -> WhyNot \c2d -> fun' a2b (d2a (fun' c2d c)) != nb
      R -> \(Ur (c2d :: c ⊸ d)) -> lol \case
        L -> \d2a -> (\c -> fun' a2b (d2a (fun' c2d c))) :: c %m -> b
        R -> linear \case
         (Nofun c nb :: Nofun m b c) ->
           Nofun (fun' c2d c) (contra' a2b nb) :: Nofun m a d

instance Profunctor (FUN m) where
  dimap' = lol \case
    L -> \nf -> apartR nf & \case
      Ur c2d :-#> nh -> apartR nh & \case
        b2c :-#> Nofun a nd -> contra' c2d nd & \nc -> 
          WhyNot \a2b -> b2c (fun' a2b a) != nc
    R -> \(Ur (a2b :: a ⊸ b)) -> lol \case
      L -> \ng -> apartR ng & linear \(b2c :-#> Nofun a nd) ->
        WhyNot \(c2d :: c ⊸ d) -> 
          b2c != (Nofun (fun' a2b a) (contra' c2d nd) :: Nofun m c b)
      R -> \(Ur (c2d :: c ⊸ d)) -> lol \case
        R -> go where
          go :: (b %m -> c) %1 -> a %m -> d
          go b2c a = fun' c2d (b2c (fun' a2b a))
        L -> go where
          go :: Nofun m d a %1 -> Nofun m c b
          go (Nofun a nd) = Nofun (fun' a2b a) (contra' c2d nd)

instance Profunctor (⊃) where
  dimap' = lol \case
    L -> \ni -> apartR ni & \((Ur c2d) :-#> nj) ->
      apartR nj & \(bic :-#> Noimp a nd) ->
        WhyNot \a2b -> bic != Noimp (fun' a2b a) (contra' c2d nd)
    R -> \(Ur (a2b :: a  ⊸ b)) -> lol \case
      L -> \ng -> apartR ng & \(bic :-#> Noimp a nd) ->
        WhyNot \c2d -> bic != Noimp (fun' a2b a) (contra' c2d nd)
      R -> \(Ur (c2d :: c ⊸ d)) -> lol \case
        L -> linear \(Noimp a nd) -> Noimp (fun' a2b a) (contra' c2d nd)
        R -> \bic -> imp \case
          L -> linear \nd -> WhyNot \a -> bic != Noimp (fun' a2b a) (contra' c2d nd)
          R -> \a -> fun' c2d (impR' bic (fun' a2b a))

class Profunctor t => MProfunctor t where
  mdimap
    :: (Prop a, Prop b, Prop c, Prop d, Lol l, Lol l', Lol l'')
    => l (a ⊸ b) (l' (c ⊸ d) (l'' (t b c) (t a d)))

instance MProfunctor (⊸) where
  mdimap = lol \case
    L -> \ni -> apartR ni & \(c2d :-#> nj) ->
      apartR nj & \(b2c :-#> a :-#> nd) ->
        a :-#> contra' b2c (contra' c2d nd)
    R -> \a2b -> lol \case
      L -> \nk -> apartR nk & \(b2c :-#> a :-#> nd) -> fun' b2c (fun' a2b a) :-#> nd
      R -> \c2d -> lol \case
        L -> \(a :-#> nd) -> fun' a2b a :-#> contra' c2d nd
        R -> \b2c -> lol \case
          L -> \nd -> contra' a2b (contra' b2c (contra' c2d nd))
          R -> \a -> fun' c2d (fun' b2c (fun' a2b a))

class
  ( forall a. Prop a => Functor (t a)
  ) => Bifunctor t where
  bimap'
    :: (Prop a, Prop b, Prop c, Prop d, Lol l, Lol l', Lol l'')
    => l (Ur (a ⊸ b)) (l' (Ur (c ⊸ d)) (l'' (t a c) (t b d)))

bimap
  :: (Bifunctor t, Prop a, Prop b, Prop c, Prop d, Lol l)
  => (a ⊸ b) -> (c ⊸ d) -> l (t a c) (t b d)
bimap f g = bimap' (Ur f) (Ur g)

bimapIso'
  :: (Bifunctor t, Prop a, Prop b, Prop c, Prop d, Lol l, Lol l', Iso i)
  => l (Ur (a ⧟ b)) (l' (Ur (c ⧟ d)) (i (t a c) (t b d)))
bimapIso' = lol \case
  L -> \ni -> apartR ni & \(Ur cd :-#> tbc2tad) -> apart tbc2tad & \case
    ApartL ntbc tad -> whyNot \ab -> bimap (runIso ab L) (runIso cd L) tad != ntbc
    ApartR tbc ntad -> whyNot \ab -> bimap (runIso ab R) (runIso cd R) tbc != ntad
  R -> \(Ur ab) -> lol \case
    L -> \nj -> apart nj & \case
      ApartL ntbc tad -> whyNot \cd -> bimap (runIso ab L) (runIso cd L) tad != ntbc
      ApartR tbc ntad -> whyNot \cd -> bimap (runIso ab R) (runIso cd R) tbc != ntad
    R -> \(Ur cd) -> iso \case
      -- improve the type of Y used by iso so we can refine this to a single def?
      L -> bimap (runIso ab L) (runIso cd L)
      R -> bimap (runIso ab R) (runIso cd R)

bimapIso
  :: (Bifunctor t, Prop a, Prop b, Prop c, Prop d, Iso i)
  => (a ⧟ b) -> (c ⧟ d) -> i (t a c) (t b d)
bimapIso f g = bimapIso' (Ur f) (Ur g)

instance Bifunctor Either where
  bimap' = lol \case
    L -> \nf -> apartR nf & \(Ur c2d :-#> nk) ->
      apartR nk & \case
        Left a :-#> nbwnd -> WhyNot \a2b -> fun' a2b a != withL' nbwnd
        Right c :-#> nbwnd -> fun' c2d c != withR' nbwnd
    R -> \(Ur f) -> lol \case
      L -> \ng -> apartR ng & \case
        Left a :-#> nbwnd -> fun' f a != withL' nbwnd
        Right c :-#> nbwnd -> WhyNot \c2d -> fun' c2d c != withR' nbwnd
      R -> \(Ur g) -> lol \case
        L -> \nbwnd -> with \case
          L -> contra' f (withL nbwnd)
          R -> contra' g (withR nbwnd)
        R -> \case
          Left a -> Left (fun f a)
          Right c -> Right (fun g c)

instance Bifunctor (,) where
  bimap' = lol \case
    L -> \nf -> apartR nf & \(Ur c2d :-#> nk) ->
      apartR nk & \((a,c) :-#> nbpnd) -> WhyNot \a2b ->
        fun' c2d c != parR' nbpnd (fun' a2b a)
    R -> \(Ur f) -> lol \case
      L -> \ng -> apartR ng & \((a, c) :-#> nbpnd) ->
        WhyNot \c2d -> fun' f a != parL' nbpnd (fun c2d c)
      R -> \(Ur g) -> lol \case
        L -> \nbpnd -> par \case
          L -> linear \c -> contra' f (parL' nbpnd (fun g c))
          R -> linear \a -> contra' g (parR' nbpnd (fun f a))
        R -> \(a, c) -> (fun f a, fun g c)

instance Bifunctor (&) where
  bimap' = lol \case
    L -> \nf -> apartR nf & \(Ur c2d :-#> nk) ->
      apartR nk & \case
        awc :-#> Left nb -> WhyNot \a2b -> fun' a2b (withL' awc) != nb
        awc :-#> Right nd -> withR' awc != contra' c2d nd
    R -> \(Ur f) -> lol \case
      L -> \ng -> apartR ng & \case
        awc :-#> Left nb -> withL awc != contra' f nb
        awc :-#> Right nd -> WhyNot \c2d -> fun' c2d (withR awc) != nd
      R -> \(Ur g) -> lol \case
        L -> \case
          Left nb  -> Left (contra' f nb)
          Right nd -> Right (contra' g nd)
        R -> \awc -> with \case
          L -> fun f (withL' awc)
          R -> fun g (withR' awc)

instance Bifunctor (⅋) where
  bimap' = lol \case
    L -> \nf -> apartR nf & \(Ur c2d :-#> nk) ->
      apartR nk & \(apc :-#> (nb, nd)) ->
        whyNot \a2b -> parR apc (contra' a2b nb) != contra' c2d nd
    R -> \(Ur f) -> lol \case
      L -> \ng -> apartR ng & \(apc :-#> (nb, nd)) -> whyNot \c2d -> parR apc (contra' f nb) != contra' c2d nd
      R -> \(Ur g) -> lol \case
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

class (Functor f, Bifunctor p) => WeakDist f p where
  weakDist :: (Lol l, Prop b, Prop c) => l (f (p b c)) (p (f b) (f c))
  default weakDist :: (Lol l, Prop b, Prop c, Dist f p) => l (f (p b c)) (p (f b) (f c))
  weakDist = weakDist

class WeakDist f p => Dist f p where
  dist :: (Iso iso, Prop b, Prop c) => iso (f (p b c)) (p (f b) (f c))

instance Prop a => WeakDist ((,) a) (&) where
  weakDist = lol \case
    L -> \case
      Left x -> fmap left x
      Right x -> fmap right x
    R -> \case
      (a, bwc) -> with \case
        L -> (a, withL bwc)
        R -> (a, withR bwc)

-- | Hyland and de Paiva section 3.2 as @w@
interchangeTensorPar :: (Lol l, Prop a, Prop b, Prop c) => l (a * (b ⅋ c)) ((a * b) ⅋ c)
interchangeTensorPar = lol \case
  L -> \(napnb, nc) -> par \case
    L -> \bpc -> parL' napnb (parL bpc nc)
    R -> \a -> (parR' napnb a, nc)
  R -> \(a, bpc) -> par \case
    L -> \nc -> (a, parL' bpc nc)
    R -> \napnb -> parR' bpc (parR' napnb a)

-- | Hyland and dePaiva's paper on FILL in section 4 describes this map as problematic
unrestricted :: (Prop a, Prop b) => (a ⅋ b ⊸ a) ⅋ b
unrestricted = par \case
  L -> \nb -> lol \case
    L -> \na -> (na, nb)
    R -> \apb -> parL' apb nb
  R -> \(apb :-#> na) -> parR' apb na

instance Prop a => WeakDist ((,) a) Either
instance Prop a => Dist ((,) a) Either where
  dist = iso \case
    L -> lol \case
      L -> \f -> with \case
        L -> par \case
          L -> \b -> parL' f (Left b)
          R -> \a -> withL' (parR' f a)
        R -> par \case
          L -> \c -> parL' f (Right c)
          R -> \a -> withR' (parR' f a)
      R -> \case
        Left (a, b) -> (a, Left b)
        Right (a, c) -> (a, Right c)
    R -> lol \case
      L -> \q -> par \case
        L -> \case
          Left b -> parL' (withL' q) b
          Right c -> parL' (withR' q) c
        R -> \a -> with \case
          L -> parR' (withL' q) a
          R -> parR' (withR' q) a
      R -> \case
        (a, Left b) ->  Left (a, b)
        (a, Right c) -> Right (a, c)

instance Prop a => WeakDist ((⅋) a) (&)
instance Prop a => Dist ((⅋) a) (&) where
  dist = iso \case
    L -> lol \case
      L -> \case
        (na, Left nb) -> Left (na, nb)
        (na, Right nc) -> Right (na, nc)
      R -> \f -> par \case
        L -> \case
          Left nb -> parL' (withL' f) nb
          Right nc -> parL' (withR' f) nc
        R -> \na -> with \case
          L -> parR' (withL' f) na
          R -> parR' (withR' f) na
    R -> lol \case
      L -> \case
        Left (na, nb) -> (na, Left nb)
        Right (na, nc) -> (na, Right nc)
      R -> \f -> with \case
         L -> fmap withL f
         R -> fmap withR f


-- utilities

--------------------------------------------------------------------------------
-- swaps
--------------------------------------------------------------------------------

-- swap primitives

swapPar'' :: p ⅋ q %1 -> q ⅋ p
swapPar'' = \apb -> par \case
  L -> \na -> parR' apb na
  R -> \nb -> parL' apb nb

swapEither'' :: p + q %1 -> q + p
swapEither'' = \case
  Left p -> Right p
  Right q -> Left q

swapWith'' :: p & q %1 -> q & p
swapWith'' w = with \case
  L -> withR' w
  R -> withL' w

swapTensor'' :: (p, q) %1 -> (q, p)
swapTensor'' = \(p,q) -> (q,p)

-- swap lolis

swapPar' :: Lol l => l (p ⅋ q) (q ⅋ p)
swapPar' = lol \case
  L -> swapTensor''
  R -> swapPar''

swapEither' :: Lol l => l (p + q) (q + p)
swapEither' = lol \case
  L -> swapWith''
  R -> swapEither''

swapWith' :: Lol l => l (p & q) (q & p)
swapWith' = lol \case
  L -> swapEither''
  R -> swapWith''

swapTensor' :: Lol l => l (p * q) (q * p)
swapTensor' = lol \case
  L -> swapPar''
  R -> swapTensor''

-- swap isos

swapPar :: Iso l => l (p ⅋ q) (q ⅋ p)
swapPar = iso \case L -> swapPar'; R -> swapPar'

swapEither :: Iso l => l (p + q) (q + p)
swapEither =  iso \case L -> swapEither'; R -> swapEither'

swapWith :: Iso l => l (p & q) (q & p)
swapWith =  iso \case L -> swapWith'; R -> swapWith'

swapTensor :: Iso l => l (p * q) (q * p)
swapTensor =  iso \case L -> swapTensor'; R -> swapTensor'

--------------------------------------------------------------------------------
-- associativity
--------------------------------------------------------------------------------

-- associtivity primitives

assocEither'' :: (a + b) + c %1 -> a + (b + c)
assocEither'' = \case
  Left (Left a) -> Left a
  Left (Right b) -> Right (Left b)
  Right c -> Right (Right c)
{-# inline assocEither'' #-}

assocTensor'' :: ((a, b), c) %1 -> (a, (b, c))
assocTensor'' = \((a, b), c) -> (a, (b, c))
{-# inline assocTensor'' #-}

assocWith'' :: (a & b) & c %1 -> a & (b & c)
assocWith'' = \abc -> with \case
  L -> withL' (withL' abc)
  R -> with \case
    L -> withR' (withL' abc)
    R -> withR' abc
{-# inline assocWith'' #-}

assocPar'' :: (a ⅋ b) ⅋ c %1 -> a ⅋ (b ⅋ c)
assocPar'' = \apb_c -> par \case
  L -> \(nb, nc) -> parL' (parL' apb_c nc) nb
  R -> \na -> par \case
    L -> \nc -> parR' (parL' apb_c nc) na
    R -> \nb -> parR' apb_c (na,nb)
{-# inline assocPar'' #-}

unassocWith'' :: a & (b & c) %1 -> (a & b) & c
unassocWith'' = \abc -> with \case
  L -> with \case
    L -> withL' abc
    R -> withL' (withR' abc)
  R -> withR' (withR' abc)
{-# inline unassocWith'' #-}

unassocPar'' :: a ⅋ (b ⅋ c) %1 -> (a ⅋ b) ⅋ c
unassocPar'' = \a_bpc -> par \case
  L -> \nc -> par \case
    L -> \nb -> parL' a_bpc (nb,nc)
    R -> \na -> parL' (parR' a_bpc na) nc
  R -> \(na,nb) -> parR' (parR' a_bpc na) nb
{-# inline unassocPar'' #-}

unassocEither'' :: a + (b + c) %1 -> (a + b) + c
unassocEither'' = \case
  Left a -> Left (Left a)
  Right (Left b) -> Left (Right b)
  Right (Right c) -> Right c
{-# inline unassocEither'' #-}

unassocTensor'' :: (a, (b, c)) %1 -> ((a, b), c)
unassocTensor'' = \(na,(nb,nc)) -> ((na,nb),nc)
{-# inline unassocTensor'' #-}

-- associativity lollipops

assocWith' :: Lol l => l ((a & b) & c) (a & (b & c))
assocWith' = lol \case L -> unassocEither''; R -> assocWith''

assocEither' :: Lol l => l ((a + b) + c) (a + (b + c))
assocEither' = lol \case L -> unassocWith''; R -> assocEither''

unassocWith' :: Lol l => l (a & (b & c)) ((a & b) & c)
unassocWith' = lol \case L -> assocEither''; R -> unassocWith''

unassocEither' :: Lol l => l (a + (b + c)) ((a + b) + c)
unassocEither' = lol \case L -> assocWith''; R -> unassocEither''

assocPar' :: Lol l => l ((a ⅋ b) ⅋ c) (a ⅋ (b ⅋ c))
assocPar' = lol \case L -> unassocTensor''; R -> assocPar''

assocTensor' :: Lol l => l ((a * b) * c) (a * (b * c))
assocTensor' = lol \case L -> unassocPar''; R -> assocTensor''

unassocPar' :: Lol l => l (a ⅋ (b ⅋ c)) ((a ⅋ b) ⅋ c)
unassocPar' = lol \case L -> assocTensor''; R -> unassocPar''

unassocTensor' :: Lol l => l (a * (b * c)) ((a * b) * c)
unassocTensor' = lol \case L -> assocPar''; R -> unassocTensor''

-- associativity isos

assocEither :: Iso i => i ((a + b) + c) (a + (b + c))
assocEither = iso \case L -> unassocEither'; R -> assocEither'

unassocEither :: Iso i => i (a + (b + c)) ((a + b) + c)
unassocEither = iso \case L -> assocEither'; R -> unassocEither'

assocWith :: Iso i => i ((a & b) & c) (a & (b & c))
assocWith = iso \case L -> unassocWith'; R -> assocWith'

unassocWith :: Iso i => i (a & (b & c)) ((a & b) & c)
unassocWith = iso \case L -> assocWith'; R -> unassocWith'

assocTensor :: Iso i => i ((a * b) * c) (a * (b * c))
assocTensor = iso \case L -> unassocTensor'; R -> assocTensor'

unassocTensor :: Iso i => i (a * (b * c)) ((a * b) * c)
unassocTensor = iso \case L -> assocTensor'; R -> unassocTensor'

assocPar :: Iso i => i ((a ⅋ b) ⅋ c) (a ⅋ (b ⅋ c))
assocPar = iso \case L -> unassocPar'; R -> assocPar'

unassocPar :: Iso i => i (a ⅋ (b ⅋ c)) ((a ⅋ b) ⅋ c)
unassocPar = iso \case L -> assocPar'; R -> unassocPar'

--------------------------------------------------------------------------------
-- * lambda & rho
--------------------------------------------------------------------------------

lambdaWith'' :: a %1 -> Top & a
lambdaWith'' = \a -> with \case
  L -> Top a
  R -> a

rhoWith'' :: a %1 -> a & Top
rhoWith'' = \b -> with \case
  L -> b
  R -> Top b

lambdaEither'' :: a %1 -> Void + a
lambdaEither'' = Right

rhoEither'' :: a %1 -> a + Void
rhoEither'' = Left

lambdaPar'' :: Prop a => a %1 -> Bot ⅋ a
lambdaPar'' = \a -> par \case
  L -> \na -> a != na
  R -> \() -> a

rhoPar'' :: Prop a => a %1 -> a ⅋ Bot
rhoPar'' = \b -> par \case
  L -> \() -> b
  R -> \nb -> b != nb

lambdaTensor'' :: a %1 -> () * a
lambdaTensor'' = ((),)

rhoTensor'' :: a %1 -> a * ()
rhoTensor'' = (,())

unlambdaPar'' :: Bot ⅋ a %1 -> a
unlambdaPar'' = \bpa -> parR' bpa ()

unrhoPar'' :: a ⅋ Bot %1 -> a
unrhoPar'' = \apb -> parL' apb ()

unlambdaTensor'' :: ((),a) %1 -> a
unlambdaTensor'' = \((),a) -> a

unrhoTensor'' :: (a,()) %1 -> a
unrhoTensor'' = \(na,()) -> na

unlambdaEither'' :: Either Void a %1 -> a
unlambdaEither'' = \case
  Right na -> na
  Left v -> \case{} v

unrhoEither'' :: Either a Void %1 -> a
unrhoEither'' = \case
  Left na -> na
  Right v -> \case{} v

unlambdaWith'' :: Top & a %1 -> a
unlambdaWith'' = withR'

unrhoWith'' :: a & Top %1 -> a
unrhoWith'' = withL

-- left unitor lolis

unlambdaEither' :: Lol l => l (Void + a) a
unlambdaEither' = lol \case L -> lambdaWith''; R -> unlambdaEither''

lambdaEither' :: Lol l => l a (Void + a)
lambdaEither' = lol \case L -> unlambdaWith''; R -> lambdaEither''

unlambdaWith' :: Lol l => l (Top & a) a
unlambdaWith' = lol \case L -> lambdaEither''; R -> unlambdaWith''

lambdaWith' :: Lol l => l a (Top & a)
lambdaWith' = lol \case L -> unlambdaEither''; R -> lambdaWith''

unlambdaTensor' :: (Lol l, Prop a) => l (() * a) a
unlambdaTensor' = lol \case L -> lambdaPar''; R -> unlambdaTensor''

lambdaTensor' :: Lol l => l a (() * a)
lambdaTensor' = lol \case L -> unlambdaPar''; R -> lambdaTensor''

unlambdaPar' :: Lol l => l (Bot ⅋ a) a
unlambdaPar' = lol \case L -> lambdaTensor''; R -> unlambdaPar''

lambdaPar' :: (Lol l, Prop a) => l a (Bot ⅋ a)
lambdaPar' = lol \case L -> unlambdaTensor''; R -> lambdaPar''

-- left unitor isos

lambdaPar :: (Iso i, Prop a) => i a (Bot ⅋ a)
lambdaPar = iso \case L -> unlambdaPar'; R -> lambdaPar'

unlambdaPar :: (Iso i, Prop a) => i (Bot ⅋ a) a
unlambdaPar = iso \case L -> lambdaPar'; R -> unlambdaPar'

lambdaWith :: Iso i => i a (Top & a)
lambdaWith = iso \case L -> unlambdaWith'; R -> lambdaWith'

unlambdaWith :: Iso i => i (Top & a) a
unlambdaWith = iso \case L -> lambdaWith'; R -> unlambdaWith'

lambdaEither :: Iso i => i a (Void + a)
lambdaEither = iso \case L -> unlambdaEither'; R -> lambdaEither'

unlambdaEither :: Iso i => i (Void + a) a
unlambdaEither = iso \case L -> lambdaEither'; R -> unlambdaEither'

lambdaTensor :: (Iso i, Prop a) => i a (() * a)
lambdaTensor = iso \case L -> unlambdaTensor'; R -> lambdaTensor'

unlambdaTensor :: (Iso i, Prop a) => i (() * a) a
unlambdaTensor = iso \case L -> lambdaTensor'; R -> unlambdaTensor'

-- rho

unrhoEither' :: Lol l => l (a + Void) a
unrhoEither' = lol \case L -> rhoWith''; R -> unrhoEither''

rhoEither' :: Lol l => l a (a + Void)
rhoEither' = lol \case L -> unrhoWith''; R -> rhoEither''

unrhoWith' :: Lol l => l (a & Top) a
unrhoWith' = lol \case L -> rhoEither''; R -> unrhoWith''

rhoWith' :: Lol l => l a (a & Top)
rhoWith' = lol \case L -> unrhoEither''; R -> rhoWith''

unrhoTensor' :: (Lol l, Prop a) => l (a * ()) a
unrhoTensor' = lol \case L -> rhoPar''; R -> unrhoTensor''

rhoTensor' :: Lol l => l a (a * ())
rhoTensor' = lol \case L -> unrhoPar''; R -> rhoTensor''

unrhoPar' :: Lol l => l (a ⅋ Bot) a
unrhoPar' = lol \case L -> rhoTensor''; R -> unrhoPar''

rhoPar' :: (Lol l, Prop a) => l a (a ⅋ Bot)
rhoPar' = lol \case L -> unrhoTensor''; R -> rhoPar''

-- left unitor isos

rhoPar :: (Iso i, Prop a) => i a (a ⅋ Bot)
rhoPar = iso \case L -> unrhoPar'; R -> rhoPar'

unrhoPar :: (Iso i, Prop a) => i (a ⅋ Bot) a
unrhoPar = iso \case L -> rhoPar'; R -> unrhoPar'

rhoWith :: Iso i => i a (a & Top)
rhoWith = iso \case L -> unrhoWith'; R -> rhoWith'

unrhoWith :: Iso i => i (a & Top) a
unrhoWith = iso \case L -> rhoWith'; R -> unrhoWith'

rhoEither :: Iso i => i a (a + Void)
rhoEither = iso \case L -> unrhoEither'; R -> rhoEither'

unrhoEither :: Iso i => i (a + Void) a
unrhoEither = iso \case L -> rhoEither'; R -> unrhoEither'

rhoTensor :: (Iso i, Prop a) => i a (a * ())
rhoTensor = iso \case L -> unrhoTensor'; R -> rhoTensor'

unrhoTensor :: (Iso i, Prop a) => i (a * ()) a
unrhoTensor = iso \case L -> rhoTensor'; R -> unrhoTensor'

--------------------------------------------------------------------------------
-- isos and apartness
--------------------------------------------------------------------------------

inv'' :: Iso i => (a ⧟ b) %1 -> i b a
inv'' (Iso f) = iso \case L -> f R; R -> f L

inv' :: (Lol l, Iso i) => l (a ⧟ b) (i b a)
inv' = lol \case
  L -> \x -> swapApart' (apart x)
  R -> inv''

inv :: (Iso i) => i (a ⧟ b) (b ⧟ a)
inv = iso \case L -> inv'; R -> inv'

swapApart'' :: a # b %1 -> b # a
swapApart'' (ApartL na b) = ApartR b na
swapApart'' (ApartR a nb) = ApartL nb a

swapApart' :: Lol l => l (a # b) (b # a)
swapApart' = lol \case L -> inv''; R -> swapApart''

swapApart :: Iso iso => iso (a # b) (b # a)
swapApart = iso \case L -> swapApart'; R -> swapApart'

--------------------------------------------------------------------------------
-- currying
--------------------------------------------------------------------------------

curryTensor'
  :: (Lol l, Lol l', Lol l'', Prep a, Prep b, Prep c)
  => l ((a * b) ⊸ c) (l' a (l'' b c))
curryTensor' = lol \case
  L -> \nf -> apartR nf &
    \(a :-#> y) -> apartR y &
      \(b :-#> nc) -> (a,b) :-#> nc
  R -> \f -> lol \case
    L -> \nbc -> apartR nbc &
      \(b :-#> nc) -> parL (contra' f nc) b
    R -> \a -> lol \case
      L -> \nc -> parR (contra' f nc) a
      R -> \b -> fun f (a, b)

uncurryTensor'
  :: (Lol l, Lol l', Prep a, Prep b, Prep c)
  => l (a ⊸ b ⊸ c) (l' (a * b) c)
uncurryTensor' = lol \case
  L -> \nf -> apartR nf &
    \((a,b) :-#> nc) -> a :-#> b :-#> nc
  R -> \f -> lol \case
    L -> \nc -> par \case
      L -> \b -> contra' f (b :-#> nc)
      R -> \a -> contra' (fun f a) nc
    R -> \(a,b) -> fun (fun f a) b

curryTensor
  :: (Iso i, Prep a, Prep b, Prep c)
  => i ((a * b) ⊸ c) (a ⊸ b ⊸ c)
curryTensor = iso \case
  L -> uncurryTensor'
  R -> curryTensor'

uncurryTensor
  :: (Iso i, Prep a, Prep b, Prep c)
  => i (a ⊸ (b ⊸ c)) ((a * b) ⊸ c)
uncurryTensor = iso \case
  L -> curryTensor'
  R -> uncurryTensor'

flip'' :: (Prep a, Prep b, Prep c, Lol l, Lol l') => (a ⊸ b ⊸ c) %1 -> l b (l' a c)
flip'' f = lol \case
  L -> \nac -> apartR nac & \(a :-#> nc) -> contra' (fun' f a) nc
  R -> \b -> lol \case
    L -> \nc -> contra' f (b :-#> nc)
    R -> \a -> fun' (fun' f a) b

flip' :: (Prep a, Prep b, Prep c, Lol l, Lol l', Lol l'') => l (a ⊸ b ⊸ c) (l' b (l'' a c))
flip' = lol \case
  L -> \nbac -> apartR nbac & \(b :-#> nac) ->
    apartR nac & \(a :-#> nc) -> a :-#> b :-#> nc
  R -> flip''

flip :: (Prep a, Prep b, Prep c, Iso iso) => iso (a ⊸ b ⊸ c) (b ⊸ a ⊸ c)
flip = iso \case
  L -> flip'
  R -> flip'

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

contra'' :: forall l p q. (Lol l, Prep p, Prep q) => p ⊸ q %1 -> l (Not q) (Not p)
contra'' = \(Lol f) -> lol \case
  L -> \na -> f R na
  R -> \nb -> f L nb

contra' :: forall l l' p q. (Lol l, Lol l', Prep p, Prep q) => l (p ⊸ q) (l' (Not q) (Not p))
contra' = lol \case
  L -> \nf -> apartR nf & \(p :-#> nq) -> nq :-#> p
  R -> contra''

contra'ish :: forall l l' p q. (Lol l, Lol l', Prop p, Prop q) => l (p ⊸ q) (l' (Not q) (Not p))
contra'ish = lol \case
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

lolPar :: (Iso iso, Prep a) => (a ⊸ b) `iso` (Not a ⅋ b)
lolPar = iso \case
  L -> lol \case
    L -> \(a :-#> nb) -> (a, nb)
    R -> \(Par f) -> Lol f
  R -> lol \case
    L -> \(a, nb) -> a :-#> nb
    R -> \(Lol f) -> Par f


--class Monoidal p => EnrichedCategory p t where
--  eid :: (Lol l, Prop a) => proxy p -> I p `l` t a a
--  ecomp :: (Lol l, Prop a) => p (t b c) (t a b) `l` t a c

-- LNL ?
--
-- F :: Hask -> L
-- G :: L -> Hask are both symmetric monoidal.
--
-- F -| G   GF is a monad, FG is a comonad
--
-- F a %1 -> b     ~    a -> G b
--
-- Ur = FG 
--
-- Moggi is a monad on Hask, which internally carries linear values? 
