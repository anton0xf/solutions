module StateEx where

import Control.Monad.State

strangeSum :: [Int] -> [Int] -> StateT Int [] String
strangeSum xs ys = do
  x <- lift xs
  y <- lift ys
  st <- get
  modify (+ y)
  return $ show (x + y) ++ "_" ++ show st


strangeSum' :: [Int] -> [Int] -> StateT Int [] String
strangeSum' xs ys = do
  lift xs >>=
    (\x -> lift ys >>=
      (\y -> get >>=
        (\st -> modify (+ y) >> return (show (x + y) ++ "_" ++ show st))))

strangeSumTest :: Bool
strangeSumTest = runStateT (strangeSum [10, 20] [3, 4, 5]) 0
  == [("13_0", 3), ("14_3", 7), ("15_7", 12), ("23_12", 15), ("24_15", 19), ("25_19", 24)]


doubleAndSum :: [Int] -> StateT Int [] Int
doubleAndSum xs = do
  x <- lift xs
  modify (+ x)
  return $ x * 2

doubleAndSumTest :: Bool
doubleAndSumTest = runStateT (doubleAndSum [10..12]) 0 == [(20, 10), (22, 11), (24, 12)]
-- but I wanted [(20, 10), (22, 21), (24, 33)]
