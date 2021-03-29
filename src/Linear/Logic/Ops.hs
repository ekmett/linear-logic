{-# language LinearTypes #-}
{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language BlockArguments #-}
{-# language NoStarIsType #-}
{-# language TypeOperators #-}
{-# language Safe #-}
{-# language TupleSections #-}
{-# language EmptyCase #-}

module Linear.Logic.Ops where

import Linear.Logic

contra :: (Prep p, Prep q) => p ⊸ q %1 -> Not q ⊸ Not p
contra = \apb -> lol \case
  L -> \na -> fun apb na
  R -> \nb -> unfun apb nb

swapPar :: p ⅋ q %1 -> q ⅋ p
swapPar = \apb -> par \case
  L -> \na -> parR apb na
  R -> \nb -> parL apb nb
{-# inline swapPar #-}

swapEither :: p + q %1 -> q + p
swapEither = \case
  Left p -> Right p
  Right q -> Left q
{-# inline swapEither #-}

swapWith :: p & q %1 -> q & p
swapWith w = with \case
  L -> withR w
  R -> withL w
{-# inline swapWith #-}

swapTensor :: (p, q) %1 -> (q, p)
swapTensor = \(p,q) -> (q,p)
{-# inline swapTensor #-}

assocEither :: (a + b) + c %1 -> a + (b + c)
assocEither = \case
  Left (Left a) -> Left a
  Left (Right b) -> Right (Left b)
  Right c -> Right (Right c)
{-# inline assocEither #-}

assocTensor :: ((a, b), c) %1 -> (a, (b, c))
assocTensor = \((a, b), c) -> (a, (b, c))
{-# inline assocTensor #-}

assocWith :: (a & b) & c %1 -> a & (b & c)
assocWith = \abc -> with \case
  L -> withL (withL abc)
  R -> with \case
    L -> withR (withL abc)
    R -> withR abc
{-# inline assocWith #-}

assocPar :: (a ⅋ b) ⅋ c %1 -> a ⅋ (b ⅋ c)
assocPar = \apb_c -> par \case
  L -> \(nb, nc) -> parL (parL apb_c nc) nb
  R -> \na -> par \case
    L -> \nc -> parR (parL apb_c nc) na
    R -> \nb -> parR apb_c (na,nb)
{-# inline assocPar #-}

unassocWith :: a & (b & c) %1 -> (a & b) & c
unassocWith = \abc -> with \case
  L -> with \case
    L -> withL abc
    R -> withL (withR abc)
  R -> withR (withR abc)
{-# inline unassocWith #-}

unassocPar :: a ⅋ (b ⅋ c) %1 -> (a ⅋ b) ⅋ c
unassocPar = \a_bpc -> par \case
  L -> \nc -> par \case
    L -> \nb -> parL a_bpc (nb,nc)
    R -> \na -> parL (parR a_bpc na) nc
  R -> \(na,nb) -> parR (parR a_bpc na) nb
{-# inline unassocPar #-}

unassocEither :: a + (b + c) %1 -> (a + b) + c
unassocEither = \case
  Left a -> Left (Left a)
  Right (Left b) -> Left (Right b)
  Right (Right c) -> Right c
{-# inline unassocEither #-}

unassocTensor :: (a, (b, c)) %1 -> ((a, b), c)
unassocTensor = \(na,(nb,nc)) -> ((na,nb),nc)
{-# inline unassocTensor #-}

lambdaWith :: a %1 -> Top & a
lambdaWith = \a -> with \case
  L -> Top a
  R -> a
{-# inline lambdaWith #-}

rhoWith :: a %1 -> a & Top
rhoWith = \b -> with \case
  L -> b
  R -> Top b
{-# inline rhoWith #-}

lambdaEither :: a %1 -> Void + a
lambdaEither = Right
{-# inline lambdaEither #-}

rhoEither :: a %1 -> a + Void
rhoEither = Left
{-# inline rhoEither #-}

lambdaPar :: Prop a => a %1 -> Bot ⅋ a
lambdaPar = \a -> par \case
  L -> \na -> a != na
  R -> \() -> a
{-# inline lambdaPar #-}

rhoPar :: Prop a => a %1 -> a ⅋ Bot
rhoPar = \b -> par \case
  L -> \() -> b
  R -> \nb -> b != nb
{-# inline rhoPar #-}

lambdaTensor :: a %1 -> () * a
lambdaTensor = ((),)
{-# inline lambdaTensor #-}

rhoTensor :: a %1 -> a * ()
rhoTensor = (,())
{-# inline rhoTensor #-}

unlambdaPar :: Bot ⅋ a %1 -> a
unlambdaPar = \bpa -> parR bpa ()
{-# inline unlambdaPar #-}

unrhoPar :: a ⅋ Bot %1 -> a
unrhoPar = \apb -> parL apb ()
{-# inline unrhoPar #-}

unlambdaTensor :: ((),a) %1 -> a
unlambdaTensor = \((),a) -> a
{-# inline unlambdaTensor #-}

unrhoTensor :: (a,()) %1 -> a
unrhoTensor = \(na,()) -> na
{-# inline unrhoTensor #-}

unlambdaEither :: Either Void a %1 -> a
unlambdaEither = \case
  Right na -> na
  Left v -> \case{} v
{-# inline unlambdaEither #-}

unrhoEither :: Either a Void %1 -> a
unrhoEither = \case
  Left na -> na
  Right v -> \case{} v
{-# inline unrhoEither #-}

unlambdaWith :: Top & a %1 -> a
unlambdaWith = withR
{-# inline unlambdaWith #-}

unrhoWith :: a & Top %1 -> a
unrhoWith = withL
{-# INLINE unrhoWith #-}
