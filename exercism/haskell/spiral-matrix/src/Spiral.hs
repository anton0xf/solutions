module Spiral (spiral) where

import Data.Function ((&))
import Data.List (find)
import Data.Maybe (isJust, fromJust)

spiral :: Int -> [[Int]]
spiral size = foldl go st [1 .. (size * size)] & m & toLists size
  where st = State {
          m = []
          , sz = size
          , pos = (0, -1)
          , dir = (0, 1)
          }

data State = State {
  m :: Matrix
  , sz :: Int -- size
  , pos :: Vec  -- current position
  , dir :: Vec -- direction
  } deriving Show

type Vec = (Int, Int) -- (row, col), 0-based

plus :: Vec -> Vec -> Vec
plus (i1, j1) (i2, j2) = (i1 + i2, j1 + j2)

rotate :: Vec -> Vec
rotate (i, j) = (j, -i)

inBounds :: Vec -> Vec -> Bool
inBounds (i, j) (isz, jsz) = 0 <= i && i < isz
  && 0 <= j && j < jsz

type Matrix = [(Vec, Int)]

matrixGet :: Vec -> Matrix -> Maybe Int
matrixGet p = fmap snd . find ((== p) . fst)

go :: State -> Int -> State
go st n =
  let newSt = if shouldRotate st
             then st {dir = rotate (st & dir)}
             else st
      newPos = nextPos newSt
  in newSt {
    pos = newPos
    , m = (newPos, n) : (st & m)
    }

shouldRotate :: State -> Bool
shouldRotate st =
  let newPos = nextPos st
      size = st & sz
  in not (inBounds newPos (size, size)) || isJust (matrixGet newPos (st & m))

nextPos :: State -> Vec
nextPos st = plus (st & pos) (st & dir)

toLists :: Int -> Matrix -> [[Int]]
toLists size mx = do
  i <- [0 .. (size-1)]
  pure [ matrixGet (i, j) mx & fromJust | j <- [0 .. (size-1)] ]
  
