module FibMemo where

-- see http://www.serpentine.com/criterion/tutorial.html
import Criterion.Main

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Function
import Control.Monad.State

fib0 :: Int -> Integer
fib0 0 = 0
fib0 1 = 1
fib0 n = fib0 (n - 2) + fib0 (n - 1)

fib1 :: Int -> Integer
fib1 = (map fib [0..] !!)
  where fib 0 = 0
        fib 1 = 1
        fib n = fib1 (n - 2) + fib1 (n - 1)

fib2 :: Int -> Integer
fib2 n = let m = Map.fromList [(0, 0), (1, 1)]
             fib :: Int -> State (Map Int Integer) Integer
             fib n = do
               m <- get
               case Map.lookup n m of
                 Nothing -> do
                   fa <- fib (n - 2)
                   fb <- fib (n - 1)
                   let fn = fa + fb
                   modify (Map.insert n fn)
                   return fn
                 Just fn -> return fn
         in evalState (fib n) m

fibM :: Monad m => (Int -> m Integer) -> Int -> m Integer
fibM _ 0 = return 0
fibM _ 1 = return 1
fibM fib n = do
  fa <- fib (n - 2)
  fb <- fib (n - 1)
  return $ fa + fb
                 
fib3 :: Int -> Integer
fib3 n = let fibM' fib n = do
               m <- get
               case Map.lookup n m of
                 Just fn -> return fn
                 Nothing -> do
                   fn <- fib n
                   modify (Map.insert n fn)
                   return fn
         in evalState (fix (fibM' . fibM) n) Map.empty

-- run it by:
-- $ runghc FibMemo.hs --time-limit 0.5 --output fib-memo-benchmark.html
main :: IO ()
main = defaultMain [
      bgroup "fib0" $ map (bf fib0) [2, 4, 6, 8, 10, 12, 14, 16],
      bgroup "fib1" $ map (bf fib1) ns,
      bgroup "fib2" $ map (bf fib2) ns,
      bgroup "fib3" $ map (bf fib3) ns
  ] where bf f n = bench (show n) $ whnf f n
          ns = [4, 8, 16, 32, 64, 128, 256]
