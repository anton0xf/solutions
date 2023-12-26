{- https://stepik.org/lesson/30428/step/12?unit=11045
2.2.12. Класс типов Traversable
Сделайте тип данных -}

data Result a = Ok a | Error String
  deriving (Eq, Show)

{- представителем класса типов Traversable (и всех других необходимых классов типов). -}

instance Functor Result where
  fmap :: (a -> b) -> Result a -> Result b
  fmap _ (Error s) = Error s
  fmap f (Ok x) = Ok $ f x

instance Foldable Result where
  foldr :: (a -> b -> b) -> b -> Result a -> b
  foldr _ ini (Error _) = ini
  foldr f ini (Ok x) = f x ini

instance Traversable Result where
  sequenceA :: Applicative f => Result (f a) -> f (Result a)
  sequenceA (Ok fx) = Ok <$> fx
  sequenceA (Error s) = pure $ Error s

traverseTest :: Bool
traverseTest = traverse (\x -> [x + 2, x - 2]) (Ok 5) == [Ok 7, Ok 3]
  && traverse (\x -> [x + 2, x - 2]) (Error "!!!") == [Error "!!!"]

test :: Bool
test = traverseTest
