module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit
import GHC.Utils.Misc
import Text.Parsec hiding (space, spaces, count)
import Data.Function ((&))
import Data.List
import Data.Bifunctor
import Data.Tuple
import Data.Maybe

import Data.Map (Map, (!))
import qualified Data.Map as Map

import Data.Set (Set, (\\))
import qualified Data.Set as Set

-- part 1

inEx :: [Char]
inEx = ""

solve1Test :: Test
solve1Test = "solve1" ~: solve1 inEx ~?= 0

tests1 :: Test
tests1 = "part 1" ~: test [solve1Test]

-- part 2

solve2Test :: Test
solve2Test = "solve2" ~: solve2 inEx ~?= 0

tests2 :: Test
tests2 = "part 2" ~: test [solve2Test]

-- main

main :: IO ()
main = do
  counts <- runTestTT $ test [tests1, tests2]
  if errors counts + failures counts == 0
    then exitSuccess else exitFailure
