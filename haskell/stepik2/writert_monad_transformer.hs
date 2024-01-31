import Data.Bifunctor
import Data.Tuple
import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Fail

{- https://stepik.org/lesson/38578/step/2?unit=20503
4.1.2. Трансформер WriterT -}
newtype WriterT w m a = WriterT { runWriterT :: m (a, w) }

runWriterTTest :: Bool
runWriterTTest = runWriterT (WriterT $ Just (1, "a")) == Just (1, "a")

writer :: Monad m => m (a, w) -> WriterT w m a
writer = WriterT

{- https://stepik.org/lesson/38578/step/3?unit=20503
4.1.3. Трансформер WriterT -}
instance Functor m => Functor (WriterT w m) where
  fmap :: (a -> b) -> WriterT w m a -> WriterT w m b
  fmap f = WriterT . fmap (first f) . runWriterT

fmapTest :: Bool
fmapTest = runWriterT ((^2) <$> WriterT [(3, "A"), (4, "B")]) == [(9, "A"), (16, "B")]

{- https://stepik.org/lesson/38578/step/4?unit=20503
4.1.4. Трансформер WriterT -}
instance (Monoid w, Applicative m) => Applicative (WriterT w m) where
  pure :: a -> WriterT w m a
  pure x = WriterT $ pure (x, mempty)

  (<*>) :: WriterT w m (a -> b) -> WriterT w m a -> WriterT w m b
  -- (WriterT wf) <*> (WriterT wx) = WriterT $ swap <$> liftA2 (<*>) (swap <$> wf) (swap <$> wx)
  (WriterT wf) <*> (WriterT wx) = WriterT $ liftA2 wap wf wx
    where
      -- wap wf wx = runWriter $ (Writer wf) <*> (Writer wx)
      wap :: (a -> b, w) -> (a, w) -> (b, w)
      wap ~(f, w1) ~(x, w2) = (f x, w1 <> w2)

apTest :: Bool
apTest = runWriterT (WriterT [((+1), "+1"), ((^2), "^2")] <*> WriterT [(3, "A"), (4, "B")])
  == [(4, "+1A"), (5, "+1B"), (9, "^2A"), (16, "^2B")]

{- https://stepik.org/lesson/38578/step/6?unit=20503
4.1.6. Трансформер WriterT -}
instance (Monoid w, Monad m) => Monad (WriterT w m) where
  (>>=) :: WriterT w m a -> (a -> WriterT w m b) -> WriterT w m b
  (WriterT wx) >>= k = WriterT $ do
    ~(x, w1) <- wx
    ~(y, w2) <- runWriterT $ k x
    return (y, w1 <> w2)

bindTest :: Bool
bindTest = runWriterT (WriterT [(3, "A"), (4, "B")] >>= k)
      == [(4, "A3+1"), (6, "A3*2"), (5, "B4+1"), (8, "B4*2")]
  where k x = WriterT [(x+1, show x ++ "+1"), (x*2, show x ++ "*2")]

doTest :: Bool
doTest = runWriterT (do {x <- writer [(3, "3"), (4, "4")];
                         writer [(x+1, "+1"), (x*2, "*2")]})
  == [(4, "3+1"), (6, "3*2"), (5, "4+1"), (8, "4*2")]

instance Monoid w => MonadTrans (WriterT w) where
  lift :: Monad m => m a -> WriterT w m a
  -- lift m = WriterT $ (, mempty) <$> m
  lift = WriterT . ((, mempty) <$>)

instance (Monoid w, MonadFail m) => MonadFail (WriterT w m) where
  fail :: String -> WriterT w m a
  -- fail = lift . fail
  fail = WriterT . fail

failTest :: Bool
failTest = runWriterT (do {x <- writer [(3, "3"), (4, "4")];
                           when (x /= 3) $ fail "msg";
                           writer [(x+1, "+1"), (x*2, "*2")]})
  == [(4, "3+1"), (6, "3*2")]

-- run all test
test :: Bool
test = runWriterTTest && fmapTest && apTest && bindTest && doTest && failTest
