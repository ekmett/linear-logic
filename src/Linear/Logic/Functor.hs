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
{-# language Trustworthy #-}

-- {-# options_ghc -Wno-unused-imports #-}

module Linear.Logic.Functor where

import Data.Void
import Data.Kind
import GHC.Types
import Linear.Logic
import Linear.Logic.Ops
import Prelude.Linear hiding (id,(.),flip)
-- import Unsafe.Linear

-- Control.Category.Linear? This isn't internalized into my logic, though
class Category p where
  id :: p a a
  (.) :: p b c %1 -> p a b %1 -> p a c

instance Category (FUN 'One) where
  id x = x
  f . g = \x -> f (g x)

-- | Here we have the ability to provide more refutations, because we can walk
-- all the way back to my arrows. This is internal to my logic.
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
  fmap' :: (Prop a, Prop b, Lol l, Lol l') => l (Ur (a ⊸ b)) (l' (f a) (f b))

fmap :: (Functor f, Prop a, Prop b, Lol l) => (a ⊸ b) -> l (f a) (f b)
fmap  f = fmap' (Ur f)

instance Functor (FUN m a) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \(a2b :-#> Nofun a nc) -> WhyNot \c2b -> a2b a != runLol c2b L nc
    R -> \(Ur xb) -> lol \case
      L -> linear \(Nofun a nb) -> Nofun a (runLol xb L nb)
      R -> \a2x a -> fun' xb (a2x a)

instance Prop x => Functor ((,) x) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \((x,a) :-#> nxpnb) ->
      WhyNot \a2b -> x != parL nxpnb (fun a2b a)
    R -> \(Ur f) -> lol \case
      L -> \nxpnb -> par \case
        L -> \a -> parL' nxpnb (fun f a)
        R -> \x -> contra' f (parR' nxpnb x)
      R -> \(x, a) -> (x, fun f a)

instance Prop x => Functor ((⊸) x) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \(x2a :-#> x :-#> nb) ->
      WhyNot \a2b -> fun' a2b (fun' x2a x) != nb
    R -> \(Ur f) -> lol \case
      L -> \x -> x & \(a :-#> nb) -> a :-#> contra' f nb
      R -> linear \g -> lol \case
        L -> linear \nb -> contra' g (contra' f nb)
        R -> \a -> fun' f (fun' g a)

instance Functor Ur where
  fmap' = lol \case
    L -> \nf -> apartR nf & \(Ur a :-#> f) ->
      WhyNot \p -> because f (fun' p a)
    R -> \(Ur f) -> lol \case
      L -> \(WhyNot cb) -> WhyNot \a -> cb (fun f a)
      R -> \(Ur a) -> Ur (fun f a)

instance Functor WhyNot where
  fmap' = lol \case
    L -> \nf -> apartR nf & \(wna :-#> Ur nb) ->
      WhyNot \a2b -> because wna (contra' a2b nb)
    R -> \(Ur f) -> lol \case
      L -> \(Ur nb) -> Ur (contra' f nb)
      R -> \na2v -> whyNot \nb -> because na2v (contra' f nb)

instance Prop a => Functor (Either a) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \case
      Left a :-#> g -> WhyNot \_ -> a != withL g
      Right b :-#> g -> WhyNot \p -> fun' p b != withR g
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
      pwa :-#> Left np -> WhyNot \_ -> withL pwa != np
      pwa :-#> Right nb -> WhyNot \a2b -> fun' a2b (withR pwa) != nb
    R -> \(Ur f) -> lol \case
      L -> \case
        Left np -> Left np
        Right nb -> Right (contra' f nb)
      R -> \pwa -> with \case
        L -> withL pwa
        R -> fun f (withR pwa)

instance Prop a => Functor ((⅋) a) where
  fmap' = lol \case
    L -> \nf -> apartR nf & \(apc :-#> (na,nb)) ->
      WhyNot \c2b -> parR apc na != contra' c2b nb
    R -> \(Ur f) -> lol \case
      L -> \(na,nb) -> (na, contra' f nb)
      R -> \apa1 -> par \case
        L -> \nb -> parL' apa1 (contra' f nb)
        R -> \na -> fun f (parR' apa1 na)

class (Functor f, Functor g) => Adjunction f g | f -> g, g -> f where
  adj :: (Iso iso, Prop a, Prop b) => iso (f a ⊸ b) (a ⊸ g b)

instance Prop e => Adjunction ((,) e) ((⊸) e) where
  adj = iso \case
    L -> uncurryTensor' . flip
    R -> flip . curryTensor'

class
  ( forall a. Prop a => Prop (f a)
  ) => Contravariant f where
  contramap' :: (Prop a, Prop b, Lol l, Lol l') => l (Ur (a ⊸ b)) (l' (f b) (f a))

instance Prop a => Contravariant ((-#>) a) where
  contramap' = fun (contra' . fmap')

contramap :: (Contravariant f, Prop a, Prop b, Lol l) => (a ⊸ b) -> l (f b) (f a)
contramap f = contramap' (Ur f)

class
  ( forall a. Prop a => Functor (t a)
  ) => Profunctor t where
  dimap'
    :: (Prop a, Prop b, Prop c, Prop d, Lol l, Lol l', Lol l'')
    => l (Ur (a ⊸ b)) (l' (Ur (c ⊸ d)) (l'' (t b c) (t a d)))

dimap :: (Profunctor t, Prop a, Prop b, Prop c, Prop d, Lol l)
    => (a ⊸ b) -> (c ⊸ d) -> l (t b c) (t a d)
dimap f g = dimap' (Ur f) (Ur g)

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

instance Profunctor (FUN m) where
  dimap' = lol \case
    L -> \nf -> apartR nf & \case
      Ur c2d :-#> nh -> apartR nh & \(b2c :-#> Nofun a nd) ->
        contra' c2d nd & \nc -> WhyNot \a2b -> nc != b2c (fun' a2b a)
    R -> \(Ur (a2b :: a ⊸ b)) -> lol \case
      L -> \ng -> apartR ng & linear \(b2c :-#> Nofun a nd) ->
        WhyNot \(c2d :: c ⊸ d) -> b2c != (Nofun (fun' a2b a) (contra' c2d nd) :: Nofun m b c)
      R -> \(Ur (c2d :: c ⊸ d)) -> lol \case
        R -> go where
          go :: (b %m -> c) %1 -> a %m -> d
          go b2c a = fun' c2d (b2c (fun' a2b a))
        L -> go where
          go :: Nofun m a d %1 -> Nofun m b c
          go (Nofun a nd) = Nofun (fun' a2b a) (contra' c2d nd)

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
        WhyNot \a2b -> parR apc (contra' a2b nb) != contra' c2d nd
    R -> \(Ur f) -> lol \case
      L -> \ng -> apartR ng & \(apc :-#> (nb, nd)) -> WhyNot \c2d -> parR apc (contra' f nb) != contra' c2d nd
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

class (Functor f, Bifunctor p) => Dist f p where
  dist :: (Iso iso, Prop b, Prop c) => iso (f (p b c)) (p (f b) (f c))

instance Prop a => Dist ((,) a) Either where
  dist = iso \case
    L -> lol \case
      L -> \f -> with \case
        L -> par \case
          L -> \b -> parL f (Left b)
          R -> \a -> withL (parR f a)
        R -> par \case
          L -> \c -> parL f (Right c)
          R -> \a -> withR (parR f a)
      R -> \case
        Left (a,b) -> (a, Left b)
        Right (a,c) -> (a, Right c)
    R -> lol \case
      L -> \q -> par \case
        L -> \case
          Left b -> parL (withL q) b
          Right c -> parL (withR q) c
        R -> \a -> with \case
          L -> parR (withL q) a
          R -> parR (withR q) a
      R -> \case
        (a, Left b) ->  Left (a, b)
        (a, Right c) -> Right (a, c)

instance Prop a => Dist ((⅋) a) (&) where
  dist = iso \case
    L -> lol \case
      L -> \case
        (na, Left nb) -> Left (na, nb)
        (na, Right nc) -> Right (na, nc)
      R -> \f -> par \case
        L -> \case
          Left nb -> parL (withL f) nb
          Right nc -> parL (withR f) nc
        R -> \na -> with \case
          L -> parR (withL f) na
          R -> parR (withR f) na
    R -> lol \case
      L -> \case
        Left (na,nb) -> (na, Left nb)
        Right (na,nc) -> (na, Right nc)
      R -> \f -> with \case
         L -> fmap withL f
         R -> fmap withR f
