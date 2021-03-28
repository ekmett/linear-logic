{-# language ExplicitNamespaces #-}
{-# language NoStarIsType #-}

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
, Ur(..), No(..), no
, extractUr, duplicateUr
, weakenUr, distUr
-- ? modality
, WhyNot(..), because, Why(..), why
, returnWhyNot, joinWhyNot
-- propositional functors
, Functor(..)
, Bifunctor(..)
, Monoidal(..)
, SymmetricMonoidal(..)
-- Internals
, Y(..)
) where

import Data.Unrestricted.Linear
import Data.Void
import Linear.Logic.Internal
import Prelude (Either(..))

