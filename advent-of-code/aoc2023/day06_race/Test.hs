module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit

testInput :: String
testInput = "Time:      7  15   30\n"
         ++ "Distance:  9  40  200\n"

testRaces :: [Race]
testRaces = [Race 7 9, Race 15 40, Race 30 200]

parseInputTest :: Test
parseInputTest = "parseInput" ~: parseInput testInput ~?= testRaces

timesToDistTest :: Test
timesToDistTest = "timesToDist" ~: map (timesToDist 7) [0 .. 7] ~?= [0, 6, 10, 12, 12, 10, 6, 0]

waysToWinTest :: Test
waysToWinTest = "waysToWin" ~: map waysToWin testRaces ~?= [4, 8, 9]

solve1Test :: Test
solve1Test = "solve1" ~: solve1 testRaces ~?= 288

tests1 :: Test
tests1 = test [parseInputTest, timesToDistTest, waysToWinTest, solve1Test]

-- part 2
testBigRace :: Race
testBigRace = Race {time = 71530, dist = 940200}

parseInput2Test :: Test
parseInput2Test = "parseInput2" ~: parseInput2 testInput ~?= testBigRace

solve2Test :: Test
solve2Test = "solve2" ~: solve2 testBigRace ~?= 71503

tests2 :: Test
tests2 = test [parseInput2Test, solve2Test]

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
