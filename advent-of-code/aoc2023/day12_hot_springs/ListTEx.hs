module ListTEx where

import Data.Maybe
import Control.Monad.List
import Control.Monad.State

cons :: a -> [[a]] -> [[a]]
cons x xss = do
  xs <- xss
  return $ x : xs

consTest :: Bool
consTest = cons '!' ["ab", "cd", "ef"] == ["!ab","!cd","!ef"]

conc :: [[a]] -> [[a]] -> [[a]]
conc xss yss = do
  xs <- xss
  ys <- yss
  return $ xs ++ ys

concTest :: Bool
concTest = conc ["aa", "bb"] ["CC", "DD", "EE"]
  == ["aaCC", "aaDD", "aaEE", "bbCC", "bbDD", "bbEE"]

strs1 :: ListT (State Int) [Char]
strs1 = ListT $ return ["ab", "cd", "ef"]

consCount :: a -> ListT (State Int) [a] -> ListT (State Int) [a]
consCount x mxss = do
  xs <- mxss
  modify (+1)
  return $ x : xs

consCountTest :: Bool
consCountTest = runState (runListT $ consCount '!' strs1) 0 == (["!ab", "!cd", "!ef"], 3)

concCount :: (ListT (State Int) [a]) -> (ListT (State Int) [a]) -> ListT (State Int) [a]
concCount mxss myss = do
  xs <- mxss
  ys <- myss
  modify (+1)
  return $ xs ++ ys

strs2 :: ListT (State Int) [Char]
strs2 = ListT $ return ["aa", "bb", "cc"]

strs3 :: ListT (State Int) [Char]
strs3 = ListT $ return ["DD", "EE"]

concCountTest :: Bool
concCountTest = runState (runListT $ concCount strs2 strs3) 0
  == (["aaDD", "aaEE", "bbDD", "bbEE", "ccDD", "ccEE"], 6)

doubleWithSum :: ListT (State Int) Int -> ListT (State Int) Int
doubleWithSum mxs = do
  x <- mxs
  lift $ modify (+ x)
  return $ x * 2

doubleWithSumTest :: Bool
doubleWithSumTest = runState (runListT $ doubleWithSum $ ListT $ return [10..14]) 0
  == ([20, 22, 24, 26, 28], 60)

arcs :: Eq a => [a] -> [(a, a)]
arcs xs = catMaybes $ evalState (runListT go) []
  where go = do
          x <- ListT $ return xs
          y <- ListT $ return xs
          st <- get
          if (y, x) `elem` st
            then return Nothing
            else do modify ((x, y) :)
                    return $ Just (x, y)

arcsTest :: Bool
arcsTest = arcs [0..2] == [(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]

test :: Bool
test = consTest && concTest && consCountTest && doubleWithSumTest && arcsTest
