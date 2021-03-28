{-# language ExplicitNamespaces #-}
{-# language NoStarIsType #-}

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

