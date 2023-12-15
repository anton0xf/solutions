{-
install dependency
$ cabal install --lib HUnit
run tests by 
$ runghc Test.hs
-}
module Test where

import Solution
import Text.Parsec
import System.Exit
import Test.HUnit
import Data.Function ((&))
import Data.Either

import Data.Set (Set)
import qualified Data.Set as Set

testInput :: String
testInput = "seeds: 79 14 55 13\n"
         ++ "\n"
         ++ "seed-to-soil map:\n"
         ++ "50 98 2\n"
         ++ "52 50 48\n"
         ++ "\n"
         ++ "soil-to-fertilizer map:\n"
         ++ "0 15 37\n"
         ++ "37 52 2\n"
         ++ "39 0 15\n"
         ++ "\n"
         ++ "fertilizer-to-water map:\n"
         ++ "49 53 8\n"
         ++ "0 11 42\n"
         ++ "42 0 7\n"
         ++ "57 7 4\n"
         ++ "\n"
         ++ "water-to-light map:\n"
         ++ "88 18 7\n"
         ++ "18 25 70\n"
         ++ "\n"
         ++ "light-to-temperature map:\n"
         ++ "45 77 23\n"
         ++ "81 45 19\n"
         ++ "68 64 13\n"
         ++ "\n"
         ++ "temperature-to-humidity map:\n"
         ++ "0 69 1\n"
         ++ "1 0 69\n"
         ++ "\n"
         ++ "humidity-to-location map:\n"
         ++ "60 56 37\n"
         ++ "56 93 4\n"

testSeedMap :: String
testSeedMap = "seed-to-soil map:\n"
          ++ "50 98 2\n"
          ++ "52 50 48\n"

tryParse :: Parsec String () a -> String -> a
tryParse p s = parse p "" s & fromRight undefined

convRulePTest :: Test
convRulePTest = "convRule" ~: ConvRule 50 98 2 ~=? tryParse convRuleP "50 98 2"

convMapPTest :: Test
convMapPTest = TestCase $ assertEqual "convMapP"
  (ConvMap {src = "seed", dst = "soil",
            rules = [ConvRule 50 98 2, ConvRule 52 50 48]})
  $ tryParse convMapP testSeedMap

testAlmanac :: Almanac
testAlmanac = parseInput testInput

parseInputTest :: Test
parseInputTest = "parseInput" ~: test [
  "seeds" ~: [79, 14, 55, 13] ~=? (testAlmanac & seeds),
  "maps length" ~: 7 ~=? (testAlmanac & maps & length),
  "first map" ~: tryParse convMapP testSeedMap ~=? (testAlmanac & maps & head)]

inRangeTest :: Test
inRangeTest = "inRange" ~: test [
  "before" ~: False ~=? inRange 0 (Range 3 2),
  "just before" ~: False ~=? inRange 2 (Range 3 2),
  "in" ~: True ~=? inRange 3 (Range 3 2),
  "in 2" ~: True ~=? inRange 4 (Range 3 2),
  "after" ~: False ~=? inRange 5 (Range 3 2),
  "after 2" ~: False ~=? inRange 10 (Range 3 2)]

applyConvRuleTest :: Test
applyConvRuleTest = let r = ConvRule 10 2 3
  in "applyConvRule" ~: test [
    "before" ~: Nothing ~=? applyConvRule r 1,
    "in 1" ~: Just 10 ~=? applyConvRule r 2,
    "in 2" ~: Just 12 ~=? applyConvRule r 4,
    "after" ~: Nothing ~=? applyConvRule r 5
  ]

applyConvMapTest :: Test
applyConvMapTest = let m = applyConvMap (tryParse convMapP testSeedMap)
  in "applyConvMap" ~: test [
     0 ~=? m 0,
     49 ~=? m 49,
     52 ~=? m 50,
     99 ~=? m 97,
     50 ~=? m 98,
     51 ~=? m 99,
     100 ~=? m 100,
     200 ~=? m 200,
     "map" ~: [81, 14, 57, 13] ~=? map m [79, 14, 55, 13],
     "path to location"
         ~: scanl (flip applyConvMap) 82 (maps testAlmanac)
         ~?= [82, 84, 84, 84, 77, 45, 46, 46]
   ]

applyConvMapsTest :: Test
applyConvMapsTest = "applyConvMaps"
  ~: [82, 43, 86, 35] ~=? map (applyConvMaps (maps testAlmanac)) (seeds testAlmanac)

solve1Test :: Test
solve1Test = "solve1" ~: 35 ~=? solve1 testAlmanac

tests1 :: Test
tests1 = "part 1" ~: test [convRulePTest, convMapPTest, parseInputTest, inRangeTest,
                           applyConvRuleTest, applyConvMapTest, applyConvMapsTest,
                           solve1Test]

-- part 2

intersectLTest :: Test
intersectLTest = let
    r = Range 2 3
    r1 = Range 0 1
  in "intersectL" ~: test [
     (Nothing, [r1]) ~=? intersectL r1 r,
     (Just $ Range 2 1, [Range 1 1]) ~=? intersectL (Range 1 2) r,
     (Just $ Range 2 2, [Range 1 1]) ~=? intersectL (Range 1 3) r,
     (Just r, [Range 1 1, Range 5 3]) ~=? intersectL (Range 1 7) r,
     (Just $ Range 3 2, []) ~=? intersectL (Range 3 2) r,
     (Just $ Range 3 2, [Range 5 2]) ~=? intersectL (Range 3 4) r,
     (Nothing, [Range 5 1]) ~=? intersectL (Range 5 1) r
  ]

applyConvRule'Test :: Test
applyConvRule'Test = let
    f = applyConvRule' $ ConvRule 10 2 3
    f1 = applyConvRule' $ ConvRule 50 98 2
    f2 = applyConvRule' $ ConvRule 52 50 48
  in "applyConvRule'" ~: test [
     (Nothing, [Range 0 2]) ~=? f (Range 0 2),
     (Just $ Range 10 1, [Range 1 1]) ~=? f (Range 1 2),
     (Just $ Range 10 1, []) ~=? f (Range 2 1),
     (Just $ Range 12 1, []) ~=? f (Range 4 1),
     (Nothing, [Range 5 2]) ~=? f (Range 5 2),
     (Just $ Range 50 2, [Range 1 97, Range 100 101]) ~=? f1 (Range 1 200),
     (Just $ Range 52 48, [Range 1 49]) ~=? f2 (Range 1 97),
     (Nothing, [Range 100 101]) ~=? f2 (Range 100 101)
  ]

applyConvRule''Test :: Test
applyConvRule''Test = let
    f1 = applyConvRule'' $ ConvRule 50 98 2
    f2 = applyConvRule'' $ ConvRule 52 50 48
  in "applyConvRule''" ~: test [
     f1 [Range 1 200] ~?= ([Range 50 2], [Range 1 97, Range 100 101]),
     f2 [Range 1 97] ~?= ([Range 52 48], [Range 1 49]),
     f2 [Range 100 101] ~?= ([], [Range 100 101])
  ]

applyConvMap'Test :: Test
applyConvMap'Test = let m = applyConvMap' (tryParse convMapP testSeedMap)
  in "applyConvMap'" ~: test [
     m [Range 1 49] ~?= [Range 1 49],
     m [Range 50 48] ~?= [Range 52 48],
     m [Range 1 49, Range 50 48] ~?= [Range 52 48, Range 1 49],
     m [Range 1 97] ~?= [Range 52 48, Range 1 49],
     m [Range 98 2] ~?= [Range 50 2],
     m [Range 99 1] ~?= [Range 51 1],
     m [Range 100 50, Range 200 1] ~?= [Range 100 50, Range 200 1],
     m [Range 1 200] ~?= [Range 50 2, Range 52 48, Range 1 49, Range 100 101],
     m [Range 79 14, Range 55 13] ~?= [Range 81 14, Range 57 13]
  ]

applyConvMaps'Test :: Test
applyConvMaps'Test = "applyConvMaps'" ~: test [
    "one rule" ~: applyConvMaps' [tryParse convMapP testSeedMap] [Range 1 200]
      ~?= [Range 50 2, Range 52 48, Range 1 49, Range 100 101],
    "test almanac" ~: let
        ms = maps testAlmanac
        rs = seedsToRanges $ seeds testAlmanac
        resRs = applyConvMaps' ms rs
        resPs = concatMap rangePoints resRs & Set.fromList
        resPs' = rs & concatMap rangePoints & map (applyConvMaps ms) & Set.fromList
      in resPs ~?= resPs'
  ]

solve2Test :: Test
solve2Test = "solve2" ~: solve2 testAlmanac ~?= 46

tests2 :: Test
tests2 = "part 2" ~: test [intersectLTest, applyConvRule'Test, applyConvRule''Test,
                           applyConvMap'Test, applyConvMaps'Test, solve2Test]

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
