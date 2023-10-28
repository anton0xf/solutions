{- https://stepik.org/lesson/7009/step/6?unit=1472
4.5 Рекурсивные типы данных step 6

Теперь нам нужно написать функцию avg, которая считает среднее арифметическое
всех значений в дереве. И мы хотим, чтобы эта функция осуществляла
только один проход по дереву. Это можно сделать при помощи вспомогательной функции,
возвращающей количество листьев и сумму значений в них. Реализуйте эту функцию.
-}

data Tree a = Leaf a | Node (Tree a) (Tree a)

avg :: Tree Int -> Int
avg t = s `div` c where
  (c, s) = go t
  go :: Tree Int -> (Int, Int)
  go (Leaf x) = (1, x)
  go (Node x y) = (cx + cy, sx + sy) where
    (cx, sx) = go x
    (cy, sy) = go y

testAvg :: Bool
testAvg = and [
    avg (Leaf 1) == 1,
    avg (Leaf 10) == 10,
    avg t1 == 2,
    avg t2 == 2,
    avg t3 == 3,
    avg t4 == 2] -- 1 2 2 3 4 -> 12 `div` 5 == 2
  where
    t1 = Node (Leaf 2) (Leaf 3)
    t2 = Node (Leaf 1) t1
    t3 = Node (Leaf 2) (Leaf 4)
    t4 = Node t2 t3
