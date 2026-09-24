{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Exception (Exception, evaluate, throw, try)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
import Linear.Logic.Internal (Prop(..), with)
import Linear.Logic.Y (Y(..))
import System.Exit (exitFailure)
import Test.HUnit
import Unsafe.Linear (toLinear2)

-- These signatures must compile without Prep or a second Prop constraint.
involution :: Not (Not a) :~: a
involution = Refl

backwards :: a :~: Not (Not a)
backwards = Refl

nested :: Proxy (Either (Not (Not a)) [Not (Not (Not (Not b)))])
       -> Proxy (Either a [b])
nested x = x

-- The metavariable in Not b ~ a is determined through involution, rather
-- than supplied by a type application or by the result type.
consumeNot :: Proxy (Not b) -> ()
consumeNot _ = ()

inferNot :: Proxy a -> ()
inferNot p = consumeNot p

dual :: forall a r. Prop a => Not a %1 -> a %1 -> r
dual = (!=) @(Not a)

-- These implications exercise both slots, both directions, and repeated duals.
withDual :: forall a r. Prop a => (Prop (Not a) => r) -> r
withDual x = x

viaContinuation :: forall a r. Prop a => Not a %1 -> a %1 -> r
viaContinuation = withDual @a ((!=) @(Not a))

reverseDual :: forall a r. Prop (Not a) => a %1 -> Not a %1 -> r
reverseDual = (!=) @a

dualFlipped :: forall a r. Prop a => a %1 -> Not a %1 -> r
dualFlipped = (=!) @(Not a)

explicitDual :: forall a r. (Prop a, Prop (Not a)) => Not a %1 -> a %1 -> r
explicitDual = (!=) @(Not a)

climb :: forall a r. Prop a => Not a %1 -> a %1 -> r
climb = withDual @a (withDual @(Not a) (withDual @(Not (Not a)) ((!=) @(Not a))))

compound :: forall a b r. Prop (Either a b)
         => Not (Either a b) %1 -> Either a b %1 -> r
compound = (!=) @(Not (Either a b))

aliased :: forall a b r. (Prop a, Not a ~ b) => b %1 -> a %1 -> r
aliased = (!=) @b

class Prop a => Witness a

fromSuperclass :: forall a r. Witness a => Not a %1 -> a %1 -> r
fromSuperclass = (!=) @(Not a)

-- The two dictionaries intentionally record different results, so a cast of
-- the original dictionary or an instance lookup cannot masquerade as a flip.
data Positive = Positive Int
data Negative = Negative Int
data Refutation = Refutation String Int Int deriving (Eq, Show)
instance Exception Refutation

instance Prop Positive where
  type Not Positive = Negative
  (!=) = toLinear2 (\(Positive p) (Negative n) -> throw (Refutation "positive" p n))

instance Prop Negative where
  type Not Negative = Positive
  (=!) = toLinear2 (\(Positive p) (Negative n) -> throw (Refutation "negative" n p))

instance Witness Positive

assertRefutation :: String -> Refutation -> () -> Test
assertRefutation label expected value = TestLabel label $ TestCase $ do
  actual <- try (evaluate value)
  assertEqual label (Left expected) actual

main :: IO ()
main = do
  result <- runTestTT $ TestList
    [ TestCase $ case involution @Int of Refl -> pure ()
    , TestCase $ case backwards @Bool of Refl -> pure ()
    , TestCase $ assertEqual "nested rewriting" (Proxy :: Proxy (Either Int [Bool]))
        (nested (Proxy :: Proxy (Either (Not (Not Int)) [Not (Not (Not (Not Bool)))])))
    , TestCase $ assertEqual "infer through Not" () (inferNot (Proxy :: Proxy Int))
    , assertRefutation "flip positive dictionary" (Refutation "positive" 11 22)
        (dual @Positive (Negative 22) (Positive 11))
    , assertRefutation "flip negative dictionary" (Refutation "negative" 22 11)
        (dual @Negative (Positive 11) (Negative 22))
    , assertRefutation "dual dictionary continuation" (Refutation "positive" 11 22)
        (viaContinuation @Positive (Negative 22) (Positive 11))
    , assertRefutation "reverse derivation" (Refutation "negative" 22 11)
        (reverseDual @Positive (Positive 11) (Negative 22))
    , assertRefutation "backward slot" (Refutation "positive" 11 22)
        (dualFlipped @Positive (Positive 11) (Negative 22))
    , assertRefutation "existing dual dictionary wins" (Refutation "negative" 22 11)
        (explicitDual @Positive (Negative 22) (Positive 11))
    , assertRefutation "repeated dualization" (Refutation "positive" 11 22)
        (climb @Positive (Negative 22) (Positive 11))
    , assertRefutation "compound given beats instance decomposition" (Refutation "positive" 11 22)
        (compound @Positive @Positive (with (\case L -> Negative 33; R -> Negative 22))
          (Right (Positive 11)))
    , assertRefutation "given equality" (Refutation "positive" 11 22)
        (aliased @Positive @Negative (Negative 22) (Positive 11))
    , assertRefutation "superclass source" (Refutation "positive" 11 22)
        (fromSuperclass @Positive (Negative 22) (Positive 11))
    ]
  if errors result == 0 && failures result == 0 then pure () else exitFailure
