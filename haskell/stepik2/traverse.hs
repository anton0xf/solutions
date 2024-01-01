{- https://stepik.org/lesson/31555/step/2?unit=11808
2.3.2. Законы и свойства класса Traversable -}

import Data.Maybe
import Data.List
import Data.Functor.Identity
import Data.Functor.Compose

{- Functor Laws
identity:    fmap id == id
composition: fmap (g2 . g1) == fmap g2 . fmap g1
-}

{- Traversable Laws
identity:    traverse Identity == Identity
composition: traverse (Compose . fmap g1 . g2) == Compose . fmap (traverse g1) . traverse g2
naturality:  t . traverse g == traverse (t . g)
  где
  t :: (Applicative f, Applicative g) => f a -> g a
  произвольный аппликативный гомоморфизм, т.е. удовлетворяет требовниям
  t (pure x) = pure x
  t (x <*> y) = t x <*> t y
-}

idTest :: Bool
idTest = traverse Identity xs == Identity xs
  where xs = [0..5]

{- https://stepik.org/lesson/31555/step/3?unit=11808 -}
compTest :: Bool
compTest = traverse (Compose . fmap g1 . g2) xs == (Compose . fmap (traverse g1) . traverse g2) xs
  where g1 = Just; g2 = singleton; xs = [0..5]

natTest :: Bool
natTest = t (traverse g xs) == traverse (t . g) xs
  where g = Just; t = maybeToList; xs = [0..5]

test :: Bool
test = idTest && compTest && natTest
