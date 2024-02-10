{- https://stepik.org/lesson/38578/step/6?discussion=8960923&reply=8975426&unit=20503
from discussion at 4.1.6. Трансформер WriterT -}

{-
Дан список положительных целых чисел (xs :: [Int]).
Начинаем с первого элемента x = head xs.
Далее можно прыгнуть на j = 1..x элементов вперёд и продолжить с этого места.
Т.е. рекусивно продолжем для списка xs' = drop j xs.
Заканчиваем, когда список закончился.
Для каждого такого пути считаем сумму значений x посещённых элементов списка.
Задача получить распределение этих сумм в зависисимости от выбора j,
т.е. сколько каких значений сумм получится, если пройти по всем возможным путям
-}

import Data.Map (Map)
import Data.Map qualified as Map

import Debug.Trace
import Control.Monad.Identity
import Control.Monad.State

traceWith :: (a -> String) -> a -> a
traceWith f x = trace (f x) x

drops :: Int -> [Int] -> [[Int]]
drops _ [] = [[]]
drops 0 xs = [xs]
drops n xs@(_ : xs') = xs : drops (n-1) xs'

dropsTest :: Bool
dropsTest = drops 0 [1, 2, 3] == [[1, 2, 3]]
  && drops 1 [1, 2, 3] == [[1, 2, 3], [2, 3]]
  && drops 2 [1, 2, 3] == [[1, 2, 3], [2, 3], [3]]
  && drops 3 [1, 2, 3] == [[1, 2, 3], [2, 3], [3], []]
  && drops 4 [1, 2, 3] == [[1, 2, 3], [2, 3], [3], []]

type SumsMap = Map Int Int -- sum -> count

jumps :: [Int] -> SumsMap
jumps [] = Map.singleton 0 1
jumps (x : xs) = Map.fromListWith (+) $ do
     xs' <- drops (x-1) xs
     (sum, count) <- Map.toList $ jumps xs'
     return (sum + x, count)

jumpsM :: Monad m => (Int -> [Int] -> m SumsMap) -> Int -> [Int] -> m SumsMap
jumpsM _ _ [] = return $ Map.singleton 0 1
jumpsM rec pos (x : xs) = do
    sums <- traverse (fmap Map.toList . uncurry rec)
        $ zip [(pos+1) ..] (drops (x-1) xs)
    return $ Map.fromListWith (+)
        [(sum + x, count) | (sum, count) <- concat sums]

type MemMap = Map Int SumsMap -- pos -> sums map
type MemState = State MemMap SumsMap

jumpsMem :: [Int] -> (SumsMap, MemMap)
jumpsMem xs = runState (fix (mem . jumpsM) 0 xs) Map.empty
  where mem :: (Int -> [Int] -> MemState) -> Int -> [Int] -> MemState
        mem rec pos xs = do
                  m :: MemMap <- get
                  case Map.lookup pos m of
                  -- case Map.lookup pos m of
                    Just sums -> return sums
                    Nothing -> do
                      sums <- rec pos xs
                      modify $ Map.insert pos sums
                      return sums

jumpsTest :: ([Int] -> Map Int Int) -> Bool
jumpsTest jumps = jumps [1, 1] == Map.fromList [(2, 1)]
  && jumps [1, 1, 1] == Map.fromList [(3, 1)]
  && jumps [2] == Map.singleton 2 1
  && jumps [2, 1] == Map.fromList [(2, 1), (3, 1)]
  && jumps [2, 2] == Map.fromList [(2, 1), (4, 1)]
  && jumps [2, 2, 2] == Map.fromList [(6, 1), (4, 2)]
  && jumps [2, 2, 2, 2] == Map.fromList [(4, 1), (6, 3), (8, 1)]
  && jumps [3, 2, 2] == Map.fromList [(3, 1), (5, 2), (7, 1)]

test :: Bool
test = dropsTest && jumpsTest jumps
  && jumpsTest (runIdentity . fix jumpsM 0)
  && jumpsTest (fst . jumpsMem)
