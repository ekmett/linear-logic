{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- #define LIFTED_Y 0

#ifdef LIFTED_Y
{-# LANGUAGE Safe #-}
#else
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LinearTypes #-}
{-# options_haddock not-home #-}
{-# options_ghc -Wno-incomplete-patterns #-}
#endif

module Linear.Logic.Y 
( Y(L,R)
) where

import Data.Kind

#ifdef LIFTED_Y

type Y :: i -> j -> k -> Type
type role Y nominal nominal nominal
data Y a b c where
  L :: Y a b a
  R :: Y a b b

#else

import Data.Type.Equality
import GHC.Prim
import GHC.Types
import Unsafe.Coerce

type Y' :: i -> j -> k -> Type
type role Y' nominal nominal nominal
data Y' a b c where
  L' :: Y' a b a
  R' :: Y' a b b

upY :: Y a b c %1 -> Y' a b c
upY (Y 0#) = unsafeCoerce L'
upY (Y 1#) = unsafeCoerce R'

type Y :: i -> j -> k -> TYPE 'IntRep
type role Y nominal nominal nominal
newtype Y a b c = Y Int#

pattern L :: forall i j k (a :: i) (b :: j) (c :: k). () => a ~~ c => Y a b c
pattern L <- (upY -> L') where
  L = Y 0#

pattern R :: forall i j k (a :: i) (b :: j) (c :: k). () => b ~~ c => Y a b c
pattern R <- (upY -> R') where
  R = Y 1#

{-# COMPLETE L, R #-}
#endif
