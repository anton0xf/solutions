{- https://stepik.org/lesson/38579/step/5?unit=20504
4.2.5. Трансформер StateT -}

import Control.Monad.Identity
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State

{- Нетрудно понять, что монада State более «сильна», чем монада Reader: вторая тоже, в некотором
смысле, предоставляет доступ к глобальному состоянию, но только, в отличие от первой,
не позволяет его менять. Покажите, как с помощью StateT можно эмулировать ReaderT -}

readerToStateT :: Monad m => ReaderT r m a -> StateT r m a
readerToStateT rm = StateT $ \st -> (, st) <$> runReaderT rm st

readerToStateTest :: Bool
readerToStateTest = runIdentity (evalStateT (readerToStateT $ asks (+2)) 4) == 6
  && evalStateT (readerToStateT $ asks (+2)) 4 == Just 6
  && runIdentity (runStateT (readerToStateT $ asks (+2)) 4) == (6,4)

test :: Bool
test = readerToStateTest
