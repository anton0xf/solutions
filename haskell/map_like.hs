{- https://stepik.org/lesson/7602/step/10?unit=1473
4.6 Синонимы и обертки для типов step 10

Ниже приведено определение класса MapLike типов, похожих на тип Map.
Определите представителя MapLike для типа ListMap, определенного ниже
как список пар ключ-значение. Для каждого ключа должно храниться
не больше одного значения. Функция insert заменяет старое значение новым,
если ключ уже содержался в структуре.
-}

import Prelude hiding (lookup)
import qualified Data.List as L

class MapLike m where
    empty :: m k v
    lookup :: Ord k => k -> m k v -> Maybe v
    insert :: Ord k => k -> v -> m k v -> m k v
    delete :: Ord k => k -> m k v -> m k v
    fromList :: Ord k => [(k,v)] -> m k v
    fromList [] = empty
    fromList ((k,v):xs) = insert k v (fromList xs)

newtype ListMap k v = ListMap { getListMap :: [(k,v)] }
    deriving (Eq, Show)

instance MapLike ListMap where
  empty = ListMap []
  
  lookup _ (ListMap []) = Nothing
  lookup s (ListMap ((k, v) : kvs)) = if k == s then Just v
    else lookup s (ListMap kvs)

  insert k v (ListMap []) = ListMap [(k, v)]
  insert k v (ListMap ((hk,hv):kvs)) = if k == hk
    then ListMap $ (k, v) : kvs
    else ListMap $ (hk, hv) : rest where
        rest = getListMap $ insert k v (ListMap kvs)

  delete _ (ListMap []) = ListMap []
  delete k (ListMap (h@(hk, _):kvs)) = if k == hk
    then ListMap kvs
    else ListMap $ h : rest where
        rest = getListMap $ delete k (ListMap kvs)

test :: Bool
test = fromList [(1, 'a'), (3, 'c'), (2, 'b')]
    == ListMap [(2, 'b'), (3, 'c'), (1, 'a')]

