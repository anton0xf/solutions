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

{- https://stepik.org/lesson/30428/step/7?unit=11045
2.2.7. Класс типов Traversable
Реализуйте функцию -}

traverse2list :: (Foldable t, Applicative f) => (a -> f b) -> t a -> f [b]
traverse2list h = foldr (\x acc -> (:) <$> h x <*> acc) (pure [])

{- работающую с эффектами как traverse_, , но параллельно с накоплением
эффектов «восстанавливающую» сворачиваемую структуру в виде списка: -}

traverse2listTest :: Bool
traverse2listTest = traverse2list (\x -> [x+10,x+20]) [1,2,3]
       == [[11, 12, 13], [11, 12, 23], [11, 22, 13], [11, 22, 23],
           [21, 12, 13], [21, 12, 23], [21, 22, 13], [21, 22, 23]]
  && traverse2list (\x -> [x+10,x+20]) (PreO $ Branch (Branch Nil 1 Nil) 2 (Branch Nil 3 Nil))
       == [[12, 11, 13], [12, 11, 23], [12, 21, 13], [12, 21, 23],
           [22, 11, 13], [22, 11, 23], [22, 21, 13], [22, 21, 23]]

{- https://stepik.org/lesson/30428/step/14?unit=11045
2.2.14. Класс типов Traversable
Сделайте двоичное дерево представителем класса типов Traversable
(а также всех других необходимых классов типов). -}

instance Functor Tree where
  fmap :: (a -> b) -> Tree a -> Tree b
  fmap _ Nil = Nil
  fmap f (Branch tl x tr) = Branch (fmap f tl) (f x) (fmap f tr)

-- like ZipList
instance Applicative Tree where
  pure :: a -> Tree a
  pure x = t
    where t = Branch t x t

  (<*>) :: Tree (a -> b) -> Tree a -> Tree b
  Nil <*> _ = Nil
  _ <*> Nil = Nil
  (Branch fl f fr) <*> (Branch xl x xr) = Branch (fl <*> xl) (f x) (fr <*> xr)

instance Traversable Tree where
  sequenceA :: Applicative m => Tree (m a) -> m (Tree a)
  sequenceA Nil = pure Nil
  sequenceA (Branch tl x tr) = Branch <$> sequenceA tl <*> x <*> sequenceA tr

traverseTest :: Bool
traverseTest = traverse (\x -> if odd x then Right x else Left x)
                        (Branch (Branch Nil 1 Nil) 3 Nil)
      == Right (Branch (Branch Nil 1 Nil) 3 Nil)
  && traverse (\x -> if odd x then Right x else Left x)
              (Branch (Branch Nil 1 Nil) 2 Nil)
      == Left 2

sequenceATest :: Bool
sequenceATest = sequenceA (Branch (Branch Nil [1, 2] Nil) [3] Nil)
  == [Branch (Branch Nil 1 Nil) 3 Nil, Branch (Branch Nil 2 Nil) 3 Nil]


test :: Bool
test = foldTest && traverse2listTest && traverseTest && sequenceATest
