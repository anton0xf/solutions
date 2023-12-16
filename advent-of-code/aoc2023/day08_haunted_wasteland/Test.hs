module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit
import Data.Function ((&))
import Data.List
import Data.Bifunctor
import Data.Tuple

inEx1 :: String
inEx1 = "RL\n"
      ++ "\n"
      ++ "AAA = (BBB, CCC)\n"
      ++ "BBB = (DDD, EEE)\n"
      ++ "CCC = (ZZZ, GGG)\n"
      ++ "DDD = (DDD, DDD)\n"
      ++ "EEE = (EEE, EEE)\n"
      ++ "GGG = (GGG, GGG)\n"
      ++ "ZZZ = (ZZZ, ZZZ)\n"

inEx2 :: String
inEx2 = "LLR\n"
     ++ "\n"
     ++ "AAA = (BBB, BBB)\n"
     ++ "BBB = (AAA, ZZZ)\n"
     ++ "ZZZ = (ZZZ, ZZZ)\n"

mapEx1 :: NetMap
mapEx1 = NetMap {
  commands = "RL",
  rules = [Rule "AAA" ("BBB","CCC"),
           Rule "BBB" ("DDD","EEE"),
           Rule "CCC" ("ZZZ","GGG"),
           Rule "DDD" ("DDD","DDD"),
           Rule "EEE" ("EEE","EEE"),
           Rule "GGG" ("GGG","GGG"),
           Rule "ZZZ" ("ZZZ","ZZZ")]}

mapEx2 :: NetMap
mapEx2 = NetMap {
  commands = "LLR",
  rules = [Rule "AAA" ("BBB","BBB"),
           Rule "BBB" ("AAA","ZZZ"),
           Rule "ZZZ" ("ZZZ","ZZZ")]}

rulePTest :: Test
rulePTest = "ruleP" ~: tryParse ruleP "AAA = (BBB, CCC)" ~?= Rule "AAA" ("BBB", "CCC")

parseInTest :: Test
parseInTest = "parseIn" ~: test [
  "inEx1" ~: parseIn inEx1 ~?= mapEx1,
  "inEx2" ~: parseIn inEx2 ~?= mapEx2]

runTest :: Test
runTest = "run" ~: test [
  run mapEx1 "AAA" "ZZZ" ~?= ["AAA", "CCC"],
  run mapEx2 "AAA" "ZZZ" ~?= ["AAA","BBB","AAA","BBB","AAA","BBB"]]

solve1Test :: Test
solve1Test = "solve1" ~: test [
  solve1 mapEx1 ~?= 2,
  solve1 mapEx2 ~?= 6]

tests1 :: Test
tests1 = test [rulePTest, parseInTest, runTest, solve1Test]

tests2 :: Test
tests2 = "part2" ~: True ~? "stub"

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
