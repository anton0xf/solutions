import Data.Bifunctor
import Control.Monad.Trans

{- https://stepik.org/lesson/38579/step/3?unit=20504
4.2.3. Трансформер StateT -}

newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

state :: Applicative m => (s -> (a, s)) -> StateT s m a
-- state f = StateT $ pure . f
state = StateT . (pure .)

{- https://stepik.org/lesson/38579/step/4?unit=20504
4.2.4. Трансформер StateT -}

evalStateT :: Functor m => StateT s m a -> s -> m a
evalStateT m st = fst <$> runStateT m st

execStateT :: Functor m => StateT s m a -> s -> m s
execStateT m st = snd <$> runStateT m st

{- https://stepik.org/lesson/38579/step/6?unit=20504
4.2.6. Трансформер StateT -}
instance Functor m => Functor (StateT s m) where
  fmap :: (a -> b) -> StateT s m a -> StateT s m b
  -- fmap f (StateT sx) = StateT $ \st -> first f <$> sx st
  fmap f (StateT sx) = StateT $ fmap (first f) . sx

instance Monad m => Applicative (StateT s m) where
  pure :: a -> StateT s m a
  pure x = StateT $ \st -> pure (x, st)

  (<*>) :: StateT s m (a -> b) -> StateT s m a -> StateT s m b
  (StateT sf) <*> (StateT sx) = StateT $ \st -> do
    ~(f, st1) <- sf st
    ~(x, st2) <- sx st1
    return (f x, st2)

instance Monad m => Monad (StateT s m) where
  (>>=) :: StateT s m a -> (a -> StateT s m b) -> StateT s m b
  (StateT sx) >>= k = StateT $ \st -> do
    ~(x, st1) <- sx st
    runStateT (k x) st1

{- https://stepik.org/lesson/38579/step/12?unit=20504
4.2.12. Трансформер StateT -}
instance MonadTrans (StateT s) where
  lift :: Monad m => m a -> StateT s m a
  lift m = StateT $ \st -> (, st) <$> m

{- https://stepik.org/lesson/38579/step/11?unit=20504
4.2.11. Трансформер StateT -}
instance MonadFail m => MonadFail (StateT s m) where
  fail :: String -> StateT s m a
  fail = lift . fail

{- https://stepik.org/lesson/38579/step/13?unit=20504
4.2.13. Трансформер StateT -}

get :: Applicative m => StateT s m s
get = state $ \st -> (st, st)

put :: Applicative m => s -> StateT s m ()
put st = state $ const ((), st)

modify :: Applicative m => (s -> s) -> StateT s m ()
modify f = state $ \st -> ((), f st)
