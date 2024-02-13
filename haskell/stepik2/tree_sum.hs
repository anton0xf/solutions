{- https://stepik.org/lesson/38580/step/13?unit=20505
4.3.13. Трансформер ExceptT -}

import Data.Monoid
import Data.Foldable
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Except

{- С деревом мы недавно встречались: -}

data Tree a = Leaf a | Fork (Tree a) a (Tree a)
  deriving (Show, Eq)

{- Вам на вход дано дерево, содержащее целые числа, записанные в виде строк. Ваша задача обойти
дерево in-order (левое поддерево, вершина, правое поддерево) и просуммировать числа до первой
строки, которую не удаётся разобрать функцией tryRead из прошлого задания (или до конца дерева,
если ошибок нет). Если ошибка произошла, её тоже надо вернуть.
Обходить деревья мы уже умеем, так что от вас требуется только функция go,
подходящая для такого вызова: -}

treeSum :: Tree String -> (Maybe ReadError, Integer)
treeSum t = let (err, s) = runWriter . runExceptT $ traverse_ go t
            in (maybeErr err, getSum s)
  where
    maybeErr :: Either ReadError () -> Maybe ReadError
    maybeErr = either Just (const Nothing)

treeSumTest :: Bool
treeSumTest = treeSum (Fork (Fork (Leaf "1") "2" (Leaf "oops")) "15" (Leaf "16"))
      == (Just (NoParse "oops"), 3)
  && treeSum (Fork (Fork (Leaf "1") "2" (Leaf "0")) "15" (Leaf "16")) == (Nothing, 34)

-- other definitions
data ReadError = EmptyInput | NoParse String
  deriving (Show, Eq)

tryRead :: (Monad m, Read a) => String -> ExceptT ReadError m a
tryRead "" = throwE EmptyInput
tryRead str = case filter (null . snd) $ reads str of
  [] -> throwE $ NoParse str
  [(x, "")] -> return x

-- solution
instance Foldable Tree where
  foldMap :: Monoid b => (a -> b) -> Tree a -> b
  foldMap f (Leaf x) = f x
  foldMap f (Fork t1 x t2) = foldMap f t1 <> f x <> foldMap f t2

go :: String -> ExceptT ReadError (Writer (Sum Integer)) ()
go = tryRead >=> (lift . tell . Sum) 
-- go s = do
--   n <- tryRead s
--   lift $ tell n

-- tests
test :: Bool
test = treeSumTest
