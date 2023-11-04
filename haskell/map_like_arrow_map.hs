{- https://stepik.org/lesson/7602/step/12?unit=1473
4.6 Синонимы и обертки для типов step 12

Реализуйте представителя MapLike для типа ArrowMap, определенного ниже.
-}

import Prelude hiding (lookup)
import Data.Maybe (isNothing)

class MapLike m where
    empty :: m k v
    lookup :: Ord k => k -> m k v -> Maybe v
    insert :: Ord k => k -> v -> m k v -> m k v
    delete :: Ord k => k -> m k v -> m k v
    fromList :: Ord k => [(k,v)] -> m k v

newtype ArrowMap k v = ArrowMap { getArrowMap :: k -> Maybe v }

instance MapLike ArrowMap where
  empty = ArrowMap $ const Nothing
  lookup k (ArrowMap m) = m k
  insert k v (ArrowMap m) = ArrowMap m' where
    m' searchKey = if searchKey == k then Just v else m searchKey
  delete k (ArrowMap m) = ArrowMap m' where
    m' searchKey = if searchKey == k then Nothing else m searchKey
  fromList = foldr (uncurry insert) empty

test :: Bool
test = and [
    lookup 2 m == Just 'b',
    isNothing $ lookup 4 m,
    isNothing $ lookup 2 $ delete 2 m,
    lookup 2 (insert 2 'd' m) == Just 'd'
  ]
  where
    m :: ArrowMap Integer Char = fromList [(1, 'a'), (3, 'c'), (2, 'b')]
