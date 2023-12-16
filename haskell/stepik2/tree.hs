{- https://stepik.org/lesson/30427/step/6?unit=11044
2.1.6. Класс типов Foldable -}

import Data.Maybe

{- Для реализации свертки двоичных деревьев нужно выбрать алгоритм обхода узлов дерева
(см., например, http://en.wikipedia.org/wiki/Tree_traversal).

Сделайте двоичное дерево -}

data Tree a = Nil | Branch (Tree a) a (Tree a)
  deriving (Eq, Show)

{- представителем класса типов Foldable, реализовав симметричную стратегию (in-order traversal).
Реализуйте также три другие стандартные стратегии
(pre-order traversal, post-order traversal и level-order traversal), сделав типы-обертки -}

newtype Preorder a = PreO (Tree a)
  deriving (Eq, Show)

newtype Postorder a = PostO (Tree a)
  deriving (Eq, Show)

newtype Levelorder a = LevelO (Tree a)
  deriving (Eq, Show)

{- представителями класса Foldable. -}

instance Foldable Tree where
  foldr :: (a -> b -> b) -> b -> Tree a -> b
  foldr _ z Nil = z
  foldr f z (Branch t0 x t1) = foldr f (f x (foldr f z t1)) t0

instance Foldable Preorder where
  foldr :: (a -> b -> b) -> b -> Preorder a -> b
  foldr _ z (PreO Nil) = z
  foldr f z (PreO (Branch t0 x t1)) = f x (foldr f (foldr f z (PreO t1)) (PreO t0))

instance Foldable Postorder where
  foldr :: (a -> b -> b) -> b -> Postorder a -> b
  foldr _ z (PostO Nil) = z
  foldr f z (PostO (Branch t0 x t1)) = foldr f (foldr f (f x z) (PostO t1)) (PostO t0)

tx :: Tree a -> Maybe a
tx Nil = Nothing
tx (Branch _ x _) = Just x

tbrs :: Tree a -> [Tree a]
tbrs Nil = []
tbrs (Branch t0 _ t1) = [t0, t1]

bfs :: [Tree a] -> [a]
bfs [] = []
bfs ts = mapMaybe tx ts ++ bfs (concatMap tbrs ts)

instance Foldable Levelorder where
  foldr :: (a -> b -> b) -> b -> Levelorder a -> b
  foldr _ z (LevelO Nil) = z
  foldr f z (LevelO t) = foldr f z $ bfs [t]

foldTest :: Bool
foldTest = let
      tree = Branch (Branch Nil 1 (Branch Nil 2 Nil)) 3 (Branch Nil 4 Nil)
  in foldr (:) [] tree == [1, 2,3, 4]
     && foldr (:) [] (PreO tree) == [3, 1, 2, 4]
     && foldr (:) [] (PostO tree) == [2, 1, 4, 3]
     && foldr (:) [] (LevelO tree) == [3, 1, 4, 2]

test :: Bool
test = foldTest
