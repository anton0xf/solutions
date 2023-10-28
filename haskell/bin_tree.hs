{- https://stepik.org/lesson/7009/step/5?unit=1472
4.5 Рекурсивные типы данных step 5
Тип бинарных деревьев можно описать следующим образом:

data Tree a = Leaf a | Node (Tree a) (Tree a)

Реализуйте функцию height, возвращающую высоту дерева,
и функцию size, возвращающую количество узлов в дереве (и внутренних, и листьев).
Считается, что дерево, состоящее из одного листа, имеет высоту 0.
-}

data Tree a = Leaf a | Node (Tree a) (Tree a)

foldTree :: (a -> b) -> (b -> b -> b) -> Tree a -> b
foldTree fl fn (Leaf x) = fl x
foldTree fl fn (Node x y) = fn x' y' where
  x' = foldTree fl fn x
  y' = foldTree fl fn y

height :: Tree a -> Int
height = foldTree (const 0) (\x y -> 1 + max x y)

testHeight :: Bool
testHeight = and [
    height (Leaf 1) == 0,
    height t1 == 1,
    height t2 == 2,
    height t3 == 1,
    height t4 == 3]
  where
    t1 = Node (Leaf 2) (Leaf 3)
    t2 = Node (Leaf 1) t1
    t3 = Node (Leaf 2) (Leaf 3)
    t4 = Node t2 t3

size :: Tree a -> Int
size = foldTree (const 1) (\x y -> 1 + x + y)

testSize :: Bool
testSize = and [
    size (Leaf 1) == 1,
    size t1 == 3,
    size t2 == 5,
    size t3 == 3,
    size t4 == 9]
  where
    t1 = Node (Leaf 2) (Leaf 3)
    t2 = Node (Leaf 1) t1
    t3 = Node (Leaf 2) (Leaf 3)
    t4 = Node t2 t3

test = testHeight && testSize
