{- https://stepik.org/lesson/30722/step/2?unit=11809
3.1.2. Монада Except -}

import Control.Applicative
import Control.Monad

newtype Except e a = Except { runExcept :: Either e a }
  deriving Show

except :: Either e a -> Except e a
except = Except

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

{- https://stepik.org/lesson/30722/step/3?unit=11809
3.1.3. Монада Except
Реализуйте функцию withExcept, позволящую, если произошла ошибка,
применить к ней заданное преобразование. -}

withExcept :: (e -> e') -> Except e a -> Except e' a
withExcept f (Except (Right x)) = Except $ Right x
withExcept f (Except (Left err)) = Except $ Left $ f err

{- https://stepik.org/lesson/30722/step/5?unit=11809 -}
throwE :: e -> Except e a
throwE = Except . Left

-- Law: catchE (throwE e) h = h e
catchE :: Except e0 a -> (e0 -> Except e1 a) -> Except e1 a
catchE (Except (Left err)) h = h err
catchE (Except (Right x)) _ = Except $ Right x
{- usage:
do { action1; ..; actionN } `catchE` \err -> handle -}

