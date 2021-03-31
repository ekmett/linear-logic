{-# language LinearTypes #-}
{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language BlockArguments #-}
{-# language NoStarIsType #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language TypeOperators #-}
{-# language Trustworthy #-}
{-# language TupleSections #-}
{-# language EmptyCase #-}

module Linear.Logic.Ops where

import Data.Kind
import Data.Void
import Linear.Logic.Y
import Linear.Logic.Internal
import Prelude.Linear

class Iso p where
  iso :: (forall c. Y (b ⊸ a) (a ⊸ b) c -> c) %1 -> p a b
  apart :: Not (p a b) %1 -> a # b

class Iso p => Lol p where
  lol :: (forall c. Y (Not b %1 -> Not a) (a %1 -> b) c -> c) %1 -> p a b
  apartR :: Not (p a b) %1 -> a -#> b

instance Iso (⧟) where
  iso = Iso
  apart = \x -> x

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

-- | Derive a linear function from a linear logic impliciation.
--
-- @
-- 'fun' :: forall a b. 'Prop' a => (a '⊸' b) %1 -> a %1 -> b
-- @
--
fun' :: (a ⊸ b) %1 -> (a %1 -> b)
fun' (Lol f) = lol f
{-# inline fun' #-}

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


{- nonsense
type a -&> b = Not a ⊸ b

curryWith'' :: Lol l => (a & b ⊸ c) %1 -> l a (b -&> c)
curryWith'' f = lol \case
  R -> \a -> lol \case 
    R -> \nb -> _ (fun f) a nb
  L -> _ f

-- newtype a ⊃ b = Unrestricted (Ur a ⊸ b)

-- newtype a ⇀ b = Partial (a ⊸ WhyNot b)

-- a ⇀ b = Neg a ⅋ WhyNot b ~  Ur b ⊸ Neg a

-}

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

fun :: (Lol l, Lol l') => l (a ⊸ b) (l' a b)
fun = lol \case
  L -> apartR
  R -> \(Lol f) -> lol f
{-# inline fun #-}

funIso :: (Lol l, Iso i) => l (a ⧟ b) (i a b)
funIso = lol \case
  L -> apart
  R -> \(Iso f) -> iso f

lolPar :: (Iso iso, Prep a) => (a ⊸ b) `iso` (Not a ⅋ b)
lolPar = iso \case
  L -> lol \case
    L -> \(a :-#> nb) -> (a, nb)
    R -> \(Par f) -> Lol f
  R -> lol \case
    L -> \(a, nb) -> a :-#> nb
    R -> \(Lol f) -> Par f
