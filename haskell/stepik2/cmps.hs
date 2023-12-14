{- https://stepik.org/lesson/30426/step/2?unit=11043
1.5.2. Композиция на уровне типов -}
{-# LANGUAGE TypeOperators #-}

import Data.Function ((&))
import Control.Applicative

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

{- https://stepik.org/lesson/30426/step/8?unit=11043
Applicative -}
instance (Applicative f, Applicative g) => Applicative (f |.| g) where
  pure :: a -> (|.|) f g a
  pure = Cmps . pure . pure

  (<*>) :: (f |.| g) (a -> b) -> (f |.| g) a -> (f |.| g) b
  -- (Cmps ch) <*> (Cmps cx) = Cmps $ liftA (<*>) ch <*> cx
  (Cmps ch) <*> (Cmps cx) = Cmps $ ((<*>) <$> ch) <*> cx
  -- (Cmps ch) <*> (Cmps cx) = Cmps $ liftA2 (<*>) ch cx

{- https://stepik.org/lesson/30426/step/10?unit=11043 -}
apTest :: Bool
apTest = getCmps (Cmps [Just (+1), Nothing, Just (+2)] <*> Cmps [Just 30, Just 40, Nothing])
    == [Just 31, Just 41, Nothing, Nothing, Nothing, Nothing, Just 32, Just 42, Nothing]

{- https://stepik.org/lesson/30426/step/9?unit=11043
Напишите универсальные функции -}

unCmps3 :: Functor f => (f |.| g |.| h) a -> f (g (h a))
unCmps3 = fmap getCmps . getCmps

unCmps4 :: (Functor f2, Functor f1) => (f2 |.| f1 |.| g |.| h) a -> f2 (f1 (g (h a)))
-- unCmps4 = (fmap . fmap) getCmps . fmap getCmps . getCmps
unCmps4 = fmap (fmap getCmps . getCmps) . getCmps

{- позволяющие избавляться от синтаксического шума для композиции нескольких функторов: -}

unCmpsTest :: Bool
unCmpsTest = (pure 42 :: ([] |.| [] |.| []) Int) == Cmps [Cmps [[42]]]
  && unCmps3 (pure 42 :: ([] |.| [] |.| []) Int) ==  [[[42]]]
  && unCmps3 (pure 42 :: ([] |.| Maybe |.| []) Int) == [Just [42]]
  && unCmps4 (pure 42 :: ([] |.| [] |.| [] |.| []) Int) == [[[[42]]]]

test :: Bool
test = apTest && unCmpsTest
