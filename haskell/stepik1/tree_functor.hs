{- https://stepik.org/lesson/8432/step/6?unit=2743

5.1 Класс типов Functor и законы для него step 6

Определите представителя класса Functor для бинарного дерева,
в каждом узле которого хранятся элементы типа Maybe:
-}

import Data.Functor ((<$>))

data Tree a = Leaf (Maybe a) | Branch (Tree a) (Maybe a) (Tree a)
  deriving (Show, Eq)

instance Functor Tree where
  fmap f (Leaf x) = Leaf $ f <$> x
  fmap f (Branch left x right) = Branch (f <$> left) (f <$> x) (f <$> right)

test = and [
    (words <$> Leaf Nothing) == Leaf Nothing,
    (words <$> Leaf (Just "a b")) == Leaf (Just ["a","b"]),
    fmap (+1) t1 == Branch (Leaf Nothing) Nothing (Leaf (Just 2)),
    fmap (+1) t2 == Branch (Branch (Leaf Nothing) Nothing (Leaf (Just 2)))
      (Just 3) (Leaf (Just 4)),
    fmap (const 0) t2 == Branch (Branch (Leaf Nothing) Nothing (Leaf (Just 0)))
      (Just 0) (Leaf (Just 0))
  ] where
    t1 = Branch (Leaf Nothing) Nothing (Leaf $ Just 1)
    t2 = Branch t1 (Just 2) (Leaf $ Just 3)
