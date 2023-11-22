{- https://stepik.org/lesson/8444/step/10?unit=1579
5.8 Монада State step 10 -}

import Control.Monad.State

{- Некоторое время назад мы определили тип двоичных деревьев, содержащих значения в узлах: -}

data Tree a = Leaf a | Fork (Tree a) a (Tree a)
  deriving (Eq, Show)

{- В этой задаче вам дано значение типа Tree (), иными словами, вам задана форма дерева.
Требуется пронумеровать вершины дерева данной формы, обойдя их in-order (то есть,
сначала обходим левое поддерево, затем текущую вершину, затем правое поддерево): -}

tick :: State Integer Integer
tick = do
  st <- get
  put $ st + 1
  return st

numberTree :: Tree () -> Tree Integer
numberTree t = evalState (num t) 1 where
  num (Leaf _) = fmap Leaf tick
  num (Fork t0 _ t1) = do
    t0' <- num t0
    n <- tick
    t1' <- num t1
    return $ Fork t0' n t1'

testNumberTree :: Bool
testNumberTree = numberTree leaf == Leaf 1
    && numberTree (Fork leaf () leaf) == Fork (Leaf 1) 2 (Leaf 3)
    && numberTree (Fork (Fork leaf () leaf) () leaf)
       == Fork (Fork (Leaf 1) 2 (Leaf 3)) 4 (Leaf 5)
  where leaf = Leaf ()
