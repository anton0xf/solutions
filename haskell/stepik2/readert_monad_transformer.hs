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

{- https://stepik.org/lesson/38577/step/15?unit=17396
3.4.15. Трансформер ReaderT -}

ask :: Monad m => ReaderT r m r
-- ask = ReaderT $ \r -> return r
ask = ReaderT return

asks :: Monad m => (r -> a) -> ReaderT r m a
-- asks f = ReaderT $ \r -> return (f r)
-- asks f = ReaderT (return . f)
asks = ReaderT . (return .)

local :: Monad m => (r -> r') -> ReaderT r' m a -> ReaderT r m a
-- local f (ReaderT rx) = do
--   r <- ask
--   lift $ rx $ f r
local f (ReaderT rx) = ReaderT (rx . f)

askTest :: Bool
askTest = runReaderT (do {e <- rl3; f <- lift [pred, succ]; return $ f e}) 7
      == [41, 43, 6, 8, 13, 15]
  where rl3 = ReaderT $ \env -> [42, env, env * 2]

asksTest :: Bool
asksTest = runReaderT (do {e <- asks (^2); f <- lift [pred, succ]; return $ f e}) 7 == [48, 50]

localTest :: Bool
localTest = runReaderT (do {e' <- local (^2) rl3; e <- ask; return $ e + e'}) 3 == [8, 12, 21]
  where rl3 = ReaderT $ \env -> [5, env, env * 2]


-- all tests
test :: Bool
test = -- TODO examples for first parts
  askTest && asksTest && localTest
