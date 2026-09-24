-- Run after building the tests:
-- cabal exec -- runghc -package=HUnit test/PluginRejections.hs
module Main where

import Data.List (isInfixOf)
import System.Exit (ExitCode(..), exitFailure)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Test.HUnit

compile :: Bool -> String -> String -> Test
compile shouldPass name diagnostic = TestLabel name $ TestCase $ do
  result <- timeout (20 * 1000000) $ readProcessWithExitCode "ghc"
    [ "-fno-code", "-fforce-recomp", "-dcore-lint", "-v0"
    , "-package", "linear-logic", "-fplugin", "Linear.Logic.Plugin"
    , "test/plugin-fixtures/" ++ name ++ ".hs"
    , "+RTS", "-M1G", "-RTS"
    ] ""
  case result of
    Nothing -> assertFailure "compiler did not terminate within 20 seconds"
    Just (status, out, err) ->
      if shouldPass
        then assertEqual (out ++ err) ExitSuccess status
        else do
          assertBool ("unexpectedly compiled\n" ++ out ++ err) (status /= ExitSuccess)
          assertBool ("wrong diagnostic\n" ++ out ++ err) (diagnostic `isInfixOf` err)
          assertBool ("compiler panic\n" ++ err) (not ("panic!" `isInfixOf` err))

main :: IO ()
main = do
  result <- runTestTT $ TestList
    [ compile True "Good" ""
    , compile False "WrongEquality" "Bool"
    , compile False "WrongReverseEquality" "Bool"
    , compile False "MissingDictionary" "Prop"
    , compile False "WrongDictionary" "Prop"
    , compile False "ScopedDictionary" "Prop"
    , compile False "ForeignNot" "Not"
    , compile False "OccursCheck" "Not"
    ]
  if errors result == 0 && failures result == 0 then pure () else exitFailure
