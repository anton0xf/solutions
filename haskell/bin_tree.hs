{- https://stepik.org/lesson/7009/step/5?unit=1472
4.5 Рекурсивные типы данных step 5
Тип бинарных деревьев можно описать следующим образом:

data Tree a = Leaf a | Node (Tree a) (Tree a)

Реализуйте функцию height, возвращающую высоту дерева,
и функцию size, возвращающую количество узлов в дереве (и внутренних, и листьев).
Считается, что дерево, состоящее из одного листа, имеет высоту 0.
-}

data Tree a = Leaf a | Node (Tree a) (Tree a)

height (Leaf _) = 0
height (Node a b) = 1 + max ha hb
  where ha = height a
        hb = height b

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
size (Leaf _) = 1
size (Node a b) = 1 + size a + size b

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
