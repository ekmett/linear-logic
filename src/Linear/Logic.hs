{-# language ExplicitNamespaces #-}
{-# language NoStarIsType #-}
{-# language Trustworthy #-}

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
( Prep
, Prop(Not,(!=))
-- additive conjunction, with
, type (&)(..), Top(..), type With, with, withL', withR', withL, withR
-- additive disjunction, oplus
, type (+), Void, Either(..), left, right
-- multiplicative conjunction, (,)
, type (*) -- ()
-- multiplciative disjunction, par
, type (⅋)(..), Bot(..), type Par, par, parL', parR', parL, parR
-- refutable "lollipop" implication
, type (⊸)(..)
, Lol(..), runLol, fun', fun, lolPar, contra, contra', contra''
, type (%->)
, type (<#-)(..)
-- equality and apartness
, Iso(..), runIso, contraIso, contraIso', contraIso''
, type (⧟)(..)
, type (#)(..)
-- primitive implication
, Nofun(..)
-- ! modality
, Ur(..)
, extractUr
, duplicateUr
, dupUr
, seely
-- , contraseely
, seelyTop
, weakenUr, apUr
, contractUr
-- ? modality
, WhyNot(..), because, whyNot
, returnWhyNot, joinWhyNot
, mem
, Decidable
-- Internals
, Y(..)
, linear
-- consumable
, tensorToWith
, eitherToPar

-- * infinite additives
, DWith(..), runDWith, dwith
, DSum(..)
-- * indexed propositions
, IProp(..)
, type (:&:)(..)
, type (:*:)(..)
, type (:⅋:)(..)
, type (:+:)(..)

-- somewhat dubious
, semiseely
, semiseelyUnit
) where

import Data.Dependent.Sum
import GHC.Generics
import Prelude.Linear hiding (Sum)
import Linear.Logic.Internal
import Linear.Logic.Functor
import Linear.Logic.Y
import Data.Void

