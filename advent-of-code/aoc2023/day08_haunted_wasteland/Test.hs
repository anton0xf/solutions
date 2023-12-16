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

-- part 2

inEx3 :: String
inEx3 = "LR\n"
     ++ "\n"
     ++ "11A = (11B, XXX)\n"
     ++ "11B = (XXX, 11Z)\n"
     ++ "11Z = (11B, XXX)\n"
     ++ "22A = (22B, XXX)\n"
     ++ "22B = (22C, 22C)\n"
     ++ "22C = (22Z, 22Z)\n"
     ++ "22Z = (22B, 22B)\n"
     ++ "XXX = (XXX, XXX)\n"

run2Test :: Test
run2Test = "run2" ~: run2 (parseIn inEx3)
  ~?= [["11A", "22A"],
       ["11B", "22B"],
       ["11Z", "22C"],
       ["11B", "22Z"],
       ["11Z", "22B"],
       ["11B", "22C"]]

solve2Test :: Test
solve2Test = "solve2" ~: solve2 (parseIn inEx3) ~?= 6

tests2 :: Test
tests2 = "part2" ~: test [run2Test, solve2Test]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
