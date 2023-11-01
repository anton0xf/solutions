{- https://stepik.org/lesson/7602/step/9?unit=1473
4.6 Синонимы и обертки для типов step 9
Реализуйте представителя класса типов Monoid для Maybe' a так,
чтобы mempty не был равен Maybe' Nothing.
Нельзя накладывать никаких дополнительных ограничений на тип a, кроме указанных в условии.
-}
import Data.Semigroup

instance Semigroup Bool where
  (<>) = (&&)

instance Monoid Bool where
  mempty = True

newtype Maybe' a = Maybe' { getMaybe :: Maybe a }
  deriving (Eq,Show)

instance Monoid a => Semigroup (Maybe' a) where
  (<>) :: Monoid a => Maybe' a -> Maybe' a -> Maybe' a
  Maybe' (Just x) <> Maybe' (Just y) = Maybe' $ Just $ mappend x y
  _ <> _ = Maybe' Nothing

instance Monoid a => Monoid (Maybe' a) where
    mempty :: Maybe' a
    mempty = Maybe' $ Just mempty
    mappend = (<>)

e = mempty :: Maybe' Bool
n = Maybe' Nothing :: Maybe' Bool
t = Maybe' $ Just True
f = Maybe' $ Just False

test :: Bool
test = and [
  e <> n == n, n <> e == n,
  e <> t == t, t <> e == t,
  e <> f == f, f <> e == f]
