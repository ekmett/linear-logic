{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Linear.Logic
import Linear.Logic.Functor (dist, weakDist)
import Test.HUnit
import Prelude qualified as P

testWithL :: P.Bool
testWithL =
  withL' (with (\case L -> (1 :: P.Int); R -> 2) :: P.Int & P.Int) P.== 1

testWithR :: P.Bool
testWithR =
  withR' (with (\case L -> (1 :: P.Int); R -> 2) :: P.Int & P.Int) P.== 2

testLeft :: P.Bool
testLeft =
  let f = runLol left R :: P.Int %1 -> P.Either P.Int P.Int
  in case f 1 of
    Left x -> x P.== 1
    Right _ -> P.False

testRight :: P.Bool
testRight =
  let f = runLol right R :: P.Int %1 -> P.Either P.Int P.Int
  in case f 2 of
    Left _ -> P.False
    Right x -> x P.== 2

testWithLFunctor :: P.Bool
testWithLFunctor =
  let f = runLol withL R :: P.Int & P.Int %1 -> P.Int
  in f (with (\case L -> 3; R -> 4) :: P.Int & P.Int) P.== 3

testWithRFunctor :: P.Bool
testWithRFunctor =
  let f = runLol withR R :: P.Int & P.Int %1 -> P.Int
  in f (with (\case L -> 3; R -> 4) :: P.Int & P.Int) P.== 4

testDistEitherLeft :: P.Bool
testDistEitherLeft =
  let d = dist @((,) ()) @P.Either @(⧟) @() @()
      f = runLol (runIso d R) R
  in case f ((), Left ()) of
    Left ((), ()) -> P.True
    Right _ -> P.False

testDistEitherRight :: P.Bool
testDistEitherRight =
  let d = dist @((,) ()) @P.Either @(⧟) @() @()
      f = runLol (runIso d R) R
  in case f ((), Right ()) of
    Right ((), ()) -> P.True
    Left _ -> P.False

testDistEitherInvLeft :: P.Bool
testDistEitherInvLeft =
  let d = dist @((,) ()) @P.Either @(⧟) @() @()
      f = runLol (runIso d L) R
  in case f (Left ((), ())) of
    ((), Left ()) -> P.True
    _ -> P.False

testDistEitherInvRight :: P.Bool
testDistEitherInvRight =
  let d = dist @((,) ()) @P.Either @(⧟) @() @()
      f = runLol (runIso d L) R
  in case f (Right ((), ())) of
    ((), Right ()) -> P.True
    _ -> P.False

testWeakDistEitherLeft :: P.Bool
testWeakDistEitherLeft =
  let d = weakDist @((,) ()) @P.Either @(⊸) @() @()
      f = runLol d R
  in case f ((), Left ()) of
    Left ((), ()) -> P.True
    Right _ -> P.False

testWeakDistEitherRight :: P.Bool
testWeakDistEitherRight =
  let d = weakDist @((,) ()) @P.Either @(⊸) @() @()
      f = runLol d R
  in case f ((), Right ()) of
    Right ((), ()) -> P.True
    Left _ -> P.False

main :: P.IO ()
main = do
  _ <- runTestTT (TestList
    [ TestCase (assertBool "withL'" testWithL)
    , TestCase (assertBool "withR'" testWithR)
    , TestCase (assertBool "left" testLeft)
    , TestCase (assertBool "right" testRight)
    , TestCase (assertBool "withL (Lol)" testWithLFunctor)
    , TestCase (assertBool "withR (Lol)" testWithRFunctor)
    , TestCase (assertBool "dist tensor/plus (Left)" testDistEitherLeft)
    , TestCase (assertBool "dist tensor/plus (Right)" testDistEitherRight)
    , TestCase (assertBool "dist inv tensor/plus (Left)" testDistEitherInvLeft)
    , TestCase (assertBool "dist inv tensor/plus (Right)" testDistEitherInvRight)
    , TestCase (assertBool "weakDist tensor/plus (Left)" testWeakDistEitherLeft)
    , TestCase (assertBool "weakDist tensor/plus (Right)" testWeakDistEitherRight)
    ])
  P.pure ()
