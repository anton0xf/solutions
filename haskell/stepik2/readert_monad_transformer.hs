{- https://stepik.org/lesson/38577/step/2?unit=17396
3.4.2. Трансформер ReaderT -}

import Control.Monad.Trans

newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }

reader :: Applicative m => (r -> a) -> ReaderT r m a
reader = ReaderT . (pure .)

instance Functor m => Functor (ReaderT r m) where
  fmap :: (a -> b) -> ReaderT r m a -> ReaderT r m b
  fmap f = ReaderT . (\rma r -> f <$> rma r) . runReaderT
  -- fmap f = ReaderT . (\rma -> (f <$>) . rma) . runReaderT
  -- fmap f = ReaderT . ((f <$>) .) . runReaderT

instance Applicative m => Applicative (ReaderT r m) where
  pure :: a -> ReaderT r m a
  -- pure x = ReaderT $ const $ return x
  pure = ReaderT . const . pure

  (<*>) :: ReaderT r m (a -> b) -> ReaderT r m a -> ReaderT r m b
  (ReaderT rf) <*> (ReaderT rx) = ReaderT ry
    where ry r = rf r <*> rx r

instance Monad m => Monad (ReaderT r m) where
  (>>=) :: ReaderT r m a -> (a -> ReaderT r m b) -> ReaderT r m b
  (ReaderT rx) >>= k = ReaderT ry
    where ry r = do
            x <- rx r
            runReaderT (k x) r

{- https://stepik.org/lesson/38577/step/13?unit=17396
3.4.14. Трансформер ReaderT -}
instance MonadTrans (ReaderT r) where
  lift :: Monad m => m a -> ReaderT r m a
  lift = ReaderT . const

instance MonadFail m => MonadFail (ReaderT r m) where
  fail :: String -> ReaderT r m a
  fail = lift . fail
