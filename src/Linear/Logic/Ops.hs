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

import Linear.Logic
import Prelude.Linear

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
  => i ((a * b) ⊸ c) (a ⊸ (b ⊸ c))
curryTensor = iso \case
  L -> uncurryTensor'
  R -> curryTensor'

uncurryTensor
  :: (Iso i, Prep a, Prep b, Prep c)
  => i (a ⊸ (b ⊸ c)) ((a * b) ⊸ c)
uncurryTensor = iso \case
  L -> curryTensor'
  R -> uncurryTensor'
