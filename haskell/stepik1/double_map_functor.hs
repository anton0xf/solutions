{- https://stepik.org/lesson/8432/step/8?unit=2743
5.1 Класс типов Functor и законы для него step 8

Определите представителя класса Functor для типов данных Entry и Map.
Тип Map представляет словарь, ключами которого являются пары.

В результате должно обеспечиваться следующее поведение:
fmap применяет функцию к значениям в словаре, не изменяя при этом ключи.
-}

import Data.Char (toUpper)

data Entry k1 k2 v = Entry (k1, k2) v
  deriving (Eq, Show)

newtype Map k1 k2 v = Map [Entry k1 k2 v]
  deriving (Eq, Show)

instance Functor (Entry k1 k2) where
  fmap f (Entry k v) = Entry k (f v)

instance Functor (Map k1 k2) where
  fmap f (Map m) = Map $ fmap (fmap f) m

test = test1 && test2 where
  emptyMap = Map [] :: Map Int Int String
  test1 = fmap (map toUpper) emptyMap == emptyMap
  test2 = fmap (map toUpper)
          (Map [Entry (0, 0) "origin", Entry (800, 0) "right corner"])
        == Map [Entry (0,0) "ORIGIN",Entry (800,0) "RIGHT CORNER"]
