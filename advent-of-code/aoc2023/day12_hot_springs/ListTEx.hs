module ListTEx where

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

test :: Bool
test = consTest && concTest && consCountTest
