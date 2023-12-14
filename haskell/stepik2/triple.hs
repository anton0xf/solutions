{- https://stepik.org/lesson/30427/step/4?unit=11044
2.1.4. Класс типов Foldable

Сделайте тип -}

data Triple a = Tr a a a  deriving (Eq, Show)

{- представителем класса типов Foldable -}
instance Foldable Triple where
  foldr :: (a -> b -> b) -> b -> Triple a -> b
  foldr f ini (Tr x1 x2 x3) = x1 `f` (x2 `f` (x3 `f` ini))

  foldl :: (b -> a -> b) -> b -> Triple a -> b
  foldl f ini (Tr x1 x2 x3) = ((ini `f` x1) `f` x2) `f` x3

foldrTest :: Bool
foldrTest = foldr (++) "!!" (Tr "ab" "cd" "efg") == "abcdefg!!"

foldlTest :: Bool
foldlTest = foldl (++) "!!" (Tr "ab" "cd" "efg") == "!!abcdefg"

test :: Bool
test = foldrTest && foldlTest
