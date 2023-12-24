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

{- https://stepik.org/lesson/30428/step/11?unit=11045
2.2.11. Класс типов Traversable
Сделайте тип Triple представителем класса типов Traversable -}

instance Functor Triple where
  fmap :: (a -> b) -> Triple a -> Triple b
  fmap f (Tr x y z) = Tr (f x) (f y) (f z)

instance Applicative Triple where
  pure :: a -> Triple a
  pure x = Tr x x x
  
  (<*>) :: Triple (a -> b) -> Triple a -> Triple b
  (Tr f1 f2 f3) <*> (Tr x1 x2 x3) = Tr (f1 x1) (f2 x2) (f3 x3)

instance Traversable Triple where
  sequenceA :: Applicative f => Triple (f a) -> f (Triple a)
  sequenceA (Tr fx fy fz) = Tr <$> fx <*> fy <*> fz

traversableTest :: Bool
traversableTest = foldl (++) "!!" (Tr "ab" "cd" "efg") == "!!abcdefg"
  && traverse (\x -> if x>10 then Right x else Left x) (Tr 12 14 16) == Right (Tr 12 14 16)
  && traverse (\x -> if x>10 then Right x else Left x) (Tr 12 8 4) == Left 8
  && sequenceA (Tr (Tr 1 2 3) (Tr 4 5 6) (Tr 7 8 9)) == Tr (Tr 1 4 7) (Tr 2 5 8) (Tr 3 6 9)

test :: Bool
test = foldrTest && foldlTest && traversableTest
