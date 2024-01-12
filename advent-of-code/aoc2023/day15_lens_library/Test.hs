module Test where

import Solution hiding (main)
import Test.HUnit
import System.Exit
import GHC.Utils.Misc (count, split)
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
inEx = "rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7\n"

hashTest :: Test
hashTest = "hash" ~: test [
  hash "HASH" ~?= 52,
  map hash ["rn=1", "cm-", "qp=3", "cm=2", "qp-", "pc=4", "ot=9", "ab=5", "pc-", "pc=6", "ot=7"]
    ~?= [30, 253, 97, 47, 14, 180, 9, 197, 48, 214, 231]]

solve1Test :: Test
solve1Test = "solve1" ~: solve1 inEx ~?= 1320

tests1 :: Test
tests1 = "part 1" ~: test [hashTest, solve1Test]

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
