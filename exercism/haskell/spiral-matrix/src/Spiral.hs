module Spiral (spiral) where

import Data.Function ((&))
import Data.Map (Map, (!))
import qualified Data.Map as Map

spiral :: Int -> [[Int]]
spiral size = foldl go s0 [1 .. (size * size)] & m & toLists size
  where s0 = State {
          m = Map.empty
          , pos = (0, -1)
          , dir = (0, 1)
          , steps = size
          , step = 0
          , rots = 1
          }

data State = State {
  m :: Matrix
  , pos :: Vec  -- current position
  , dir :: Vec -- direction
  , steps :: Int -- count of steps in a given direction
  , step :: Int -- current step in a given direction
  , rots :: Int -- roots until steps decreasing
  } deriving Show

type Matrix = Map Vec Int

type Vec = (Int, Int) -- (row, col), 0-based

plus :: Vec -> Vec -> Vec
plus (i1, j1) (i2, j2) = (i1 + i2, j1 + j2)

rotate :: Vec -> Vec
rotate (i, j) = (j, -i)

go :: State -> Int -> State
go s n = stepState n $ if shouldRotate s then rotateState s else s

shouldRotate :: State -> Bool
shouldRotate s = (s & step) == (s & steps)

rotateState :: State -> State
rotateState s =
  let newRots = (s & rots) - 1
  in s {
    dir = rotate (s & dir)
    , step = 0
    , steps = if newRots == 0 then (s & steps) - 1 else s & steps
    , rots = if newRots == 0 then 2 else newRots
    }

stepState :: Int -> State -> State
stepState n s =
  let newPos = plus (s & pos) (s & dir)
  in s {
    step = step s + 1
    , pos = newPos
    , m = Map.insert newPos n (s & m)
    }

toLists :: Int -> Matrix -> [[Int]]
toLists size mx = do
  i <- [0 .. (size-1)]
  pure [ mx ! (i, j) | j <- [0 .. (size-1)]]
  
