{- https://stepik.org/lesson/38581/step/10?unit=20506 -}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Functor.Identity
import Control.Monad.State

{- 4.4.10. Неявный лифтинг

В этой и следующих задачах мы продолжаем работу с трансформером LoggT
разработанным на первом уроке этой недели (see logged.hs): -}

data Logged a = Logged String a deriving (Eq, Show)

instance Functor Logged where
  fmap :: (a -> b) -> Logged a -> Logged b
  fmap f (Logged log x) = Logged log (f x)

instance Applicative Logged where
  pure :: a -> Logged a
  pure = Logged ""

  (<*>) :: Logged (a -> b) -> Logged a -> Logged b
  (Logged log1 f) <*> (Logged log2 x) = Logged (log1 ++ log2) (f x)

newtype LoggT m a = LoggT { runLoggT :: m (Logged a) }

instance Functor m => Functor (LoggT m) where
  fmap :: (a -> b) -> LoggT m a -> LoggT m b
  fmap f = LoggT . (fmap . fmap) f . runLoggT

instance Applicative m => Applicative (LoggT m) where
  pure :: a -> LoggT m a
  pure = LoggT . pure . pure

  (<*>) :: LoggT m (a -> b) -> LoggT m a -> LoggT m b
  (LoggT lf) <*> (LoggT lx) = LoggT $ (<*>) <$> lf <*> lx

instance Monad m => Monad (LoggT m) where
  (>>=) :: LoggT m a -> (a -> LoggT m b) -> LoggT m b
  (LoggT lx) >>= k = LoggT $ do
    (Logged log1 x) <- lx
    (Logged log2 y) <- runLoggT (k x)
    return $ Logged (log1 ++ log2) y

instance MonadFail m => MonadFail (LoggT m) where
  fail :: String -> LoggT m a
  fail = LoggT . fail

instance MonadTrans LoggT where
  lift :: Monad m => m a -> LoggT m a
  lift = LoggT . (Logged mempty <$>)

write2log :: Monad m => String -> LoggT m ()
write2log msg = LoggT $ return $ Logged msg ()

type Logg = LoggT Identity

runLogg :: Logg a -> Logged a
runLogg = runIdentity . runLoggT

{- Теперь мы хотим сделать этот трансформер mtl-совместимым.

Избавьтесь от необходимости ручного подъема операций вложенной монады State,
сделав трансформер LoggT, примененный к монаде с интерфейсом MonadState,
представителем этого (MonadState) класса типов: -}

instance MonadState s m => MonadState s (LoggT m) where
  get :: MonadState s m => LoggT m s
  get = lift get

  put :: MonadState s m => s -> LoggT m ()
  -- put st = do { put st; return () }
  put = lift . put
  
  state :: MonadState s m => (s -> (a, s)) -> LoggT m a
  state = lift . state
  -- state f = LoggT $ state $ \st ->
  --   let (x, st') = f st
  --   in (pure x, st')

logSt' :: LoggT (State Integer) Integer      
logSt' = do 
  modify (+1)                   -- no lift!
  a <- get                      -- no lift!
  write2log $ show $ a * 10
  put 42                        -- no lift!
  return $ a * 100

logSt'Test :: Bool
logSt'Test = runState (runLoggT logSt') 2 == (Logged "30" 300, 42)

-- tests
test :: Bool
test = logSt'Test

