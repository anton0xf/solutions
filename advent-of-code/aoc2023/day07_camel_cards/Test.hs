module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit
import Data.Function ((&))
import Data.List
import Data.Bifunctor
import Data.Tuple

testInput :: String
testInput = "32T3K 765\n"
         ++ "T55J5 684\n"
         ++ "KK677 28\n"
         ++ "KTJJT 220\n"
         ++ "QQQJA 483\n"

testBids :: [(String, Integer)]
testBids = [("32T3K", 765),
            ("T55J5", 684),
            ("KK677", 28),
            ("KTJJT", 220),
            ("QQQJA", 483)]

parseInputTest :: Test
parseInputTest = "parseInput" ~: parseInput testInput ~?= testBids

handTypeTest :: Test
handTypeTest = "handType" ~: test [
  map (handType . fst) testBids ~?= [Pair, Three, TwoPair, TwoPair, Three],
  map handType ["AAAAA", "AKKKK", "A1A1A", "AKQJT"] ~?= [Five, Four, FullHouse, High]]

rankBidsTest :: Test
rankBidsTest = "rankBids" ~: rankBids testBids
  ~?= [(1, (Hand Pair "32T3K", 765)),
       (2, (Hand TwoPair "KTJJT", 220)),
       (3, (Hand TwoPair "KK677", 28)),
       (4, (Hand Three "T55J5", 684)),
       (5, (Hand Three "QQQJA", 483))]

solve1Test :: Test
solve1Test = "solve1" ~: solve1 testBids ~?= 6440

tests1 :: Test
tests1 = test [parseInputTest, handTypeTest, rankBidsTest, solve1Test]

tests2 :: Test
tests2 = "part2" ~: True ~? "stub"

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
