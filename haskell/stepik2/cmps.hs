{- https://stepik.org/lesson/30426/step/2?unit=11043
1.5.2. Композиция на уровне типов -}
{-# LANGUAGE TypeOperators #-}

infixr 9 |.|
newtype (|.|) f g a = Cmps { getCmps :: f (g a) }
  deriving (Show, Eq)

{- https://stepik.org/lesson/30426/step/3?unit=11043
Населите допустимыми нерасходящимися выражениями следующие типы -}

type A   = ((,) Integer |.| (,) Char) Bool
type B t = ((,,) Bool (t -> t) |.| Either String) Int
type C   = (|.|) ((->) Bool) ((->) Integer) Integer

a :: A
a = Cmps (1, ('a', True))

b :: B t
b = Cmps (True, id, Left "asdf")

c :: C
c  = Cmps $ const (+1)

{- https://stepik.org/lesson/30426/step/6?unit=11043
Functor -}

instance (Functor f, Functor g) => Functor (f |.| g) where
  fmap :: (a -> b) -> (|.|) f g a -> (|.|) f g b
  fmap h = Cmps . (fmap . fmap) h . getCmps
