{- https://stepik.org/lesson/31555/step/12?unit=11808
2.3.12. Законы и свойства класса Traversable -}

import Data.List
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Sum

{- Сделайте двоичное дерево -}

data Tree a = Nil | Branch (Tree a) a (Tree a)
  deriving (Eq, Show)

{- представителем класса типов Traversable таким образом,
чтобы обеспечить для foldMapDefault порядок обхода «postorder traversal»: -}

testTree :: Tree Integer
testTree = Branch (Branch (Branch Nil 1 Nil) 2 (Branch Nil 3 Nil)) 4 (Branch Nil 5 Nil)

foldMapDefaultTest :: Bool
foldMapDefaultTest = foldMapDefault (: []) testTree == [1,3,2,5,4]

fmapDefault :: Traversable t => (a -> b) -> t a -> t b
fmapDefault f = runIdentity . traverse (Identity . f)

foldMapDefault :: (Traversable t, Monoid m) => (a -> m) -> t a -> m
foldMapDefault f = getConst . traverse (Const . f)

foldMapUsingPairEx :: Bool
foldMapUsingPairEx = (fst . traverse ((, ()) . singleton)) testTree == [1,3,2,5,4]

instance Traversable Tree where
  traverse :: Applicative m => (a -> m b) -> Tree a -> m (Tree b)
  traverse _ Nil = pure Nil
  traverse f (Branch tl x tr) = flip . Branch <$> traverse f tl <*> traverse f tr <*> f x

  -- sequenceA :: Applicative m => Tree (m a) -> m (Tree a)
  -- sequenceA Nil = pure Nil
  -- sequenceA (Branch tl x tr) = flip . Branch <$> sequenceA tl <*> sequenceA tr <*> x
  {- you cannot use only this 'sequenceA' because default traverce is
       traverse f = sequenceA . fmap f
     and 'fmap = fmapDefault' also has call to traverse -}

instance Functor Tree where
  fmap :: (a -> b) -> Tree a -> Tree b
  fmap = fmapDefault

instance Foldable Tree where
  foldMap :: Monoid m => (a -> m) -> Tree a -> m
  foldMap = foldMapDefault

test :: Bool
test = foldMapDefaultTest && foldMapUsingPairEx
