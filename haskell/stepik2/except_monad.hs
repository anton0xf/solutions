{- https://stepik.org/lesson/30722/step/2?unit=11809
3.1.2. Монада Except -}

import Control.Applicative
import Control.Monad

newtype Except e a = Except { runExcept :: Either e a }
  deriving Show

except :: Either e a -> Except e a
except = Except

throw :: e -> Except e a
throw e = Except $ Left e

-- catch :: a -> 

instance Functor (Except e) where
  fmap :: (a -> b) -> Except e a -> Except e b
  fmap = liftM

instance Applicative (Except e) where
  pure :: a -> Except e a
  pure = except . pure

  (<*>) :: Except e (a -> b) -> Except e a -> Except e b
  (<*>) = ap

instance Monad (Except e) where
  (>>=) :: Except e a -> (a -> Except e b) -> Except e b
  (Except m) >>= k = Except $ m >>= (runExcept . k)

-- instance Monoid e => Alternative (Except e) where
--   empty :: Monoid e => Except e a
--   empty = Except $ Left mempty

--   (Except m1) <|> (Except m2) = Except $ m1 <|> m2


