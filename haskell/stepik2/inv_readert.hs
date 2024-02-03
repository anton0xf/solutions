{- https://stepik.org/lesson/38578/step/2?discussion=6887339&reply=8966818
try to implement other nesting order then in ReaderT (see readert_monad_transfomer.hs) -}

import Control.Monad.Trans

newtype InvReaderT r m a = InvReaderT { runInvReaderT :: m (r -> a) }

invReader :: Applicative m => (r -> a) -> InvReaderT r m a
invReader = InvReaderT . pure

instance Functor m => Functor (InvReaderT r m) where
  fmap :: (a -> b) -> InvReaderT r m a -> InvReaderT r m b
  fmap f = InvReaderT . (\m -> (f .) <$> m) . runInvReaderT
  -- fmap f = InvReaderT . ((f .) <$>) . runInvReaderT

instance Applicative m => Applicative (InvReaderT r m) where
  pure :: a -> InvReaderT r m a
  pure = InvReaderT . pure . const

  (<*>) :: InvReaderT r m (a -> b) -> InvReaderT r m a -> InvReaderT r m b
  (InvReaderT mrf) <*> (InvReaderT mrx) = InvReaderT $ comp <$> mrf <*> mrx
    where comp rf rx r = rf r $ rx r

instance Monad m => Monad (InvReaderT r m) where
  (>>=) :: InvReaderT r m a -> (a -> InvReaderT r m b) -> InvReaderT r m b
  (InvReaderT mrx) >>= k = InvReaderT $ do
    rx <- mrx
    return $ \r -> runInvReaderT (k $ rx r)
