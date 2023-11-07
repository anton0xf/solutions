{- https://stepik.org/lesson/8437/step/8?unit=1572
5.2 Определение монады step 8
Реализованные ранее returnLog и bindLog позволяют объявить
тип Log представителем класса Monad -}

data Log a = Log [String] a deriving (Eq, Show)

toLogger :: (a -> b) -> String -> a -> Log b
toLogger f s x = Log [s] (f x)

add1Log = toLogger (+1) "added one"

mult2Log = toLogger (* 2) "multiplied by 2"

returnLog :: a -> Log a
returnLog = Log []

bindLog :: Log a -> (a -> Log b) -> Log b
bindLog (Log ss x) f = let (Log ss' y) = f x in
    Log (ss ++ ss') y

instance Functor Log where
  fmap f (Log ss x) = Log ss (f x)

instance Applicative Log where
  pure = returnLog
  (Log ss1 f) <*> (Log ss2 x) = Log (ss1 ++ ss2) $ f x

-- pure id <*> v == v
testAppIdentity = let v = Log ["test"] 1
  in (pure id <*> v) == v

-- pure (.) <*> u <*> v <*> w == u <*> (v <*> w)
testAppComposition = (pure (.) <*> u <*> v <*> w) == (u <*> (v <*> w)) where
  u = Log ["a"] (*2)
  v = Log ["b"] (+1)
  w = Log ["c"] 3

-- pure f <*> pure x == pure (f x)
testAppHomomorphism = left == right where
  x = 1 :: Integer
  f = (* 2)
  left :: Log Integer = pure f <*> pure x
  right :: Log Integer = pure (f x)

-- u <*> pure y == pure ($ y) <*> u
testAppInterchange = (u <*> pure y) == (pure ($ y) <*> u) where
  y = 3 :: Integer
  u = Log ["test"] (*4) :: Log (Integer -> Integer)

testApp = testAppIdentity && testAppComposition
  && testAppHomomorphism && testAppInterchange

instance Monad Log where
    -- return = returnLog
    (>>=) = bindLog

{- Используя return и >>=, определите функцию execLoggersList -}

execLoggersList :: a -> [a -> Log a] -> Log a
execLoggersList x = foldl (>>=) (return x)

{- которая принимает некоторый элемент, список функций с логированием
и возвращает результат последовательного применения всех функций
в списке к переданному элементу вместе со списком сообщений,
которые возвращались данными функциями: -}

testExecLoggersList = execLoggersList 3
        [add1Log, mult2Log, \x -> Log ["multiplied by 100"] (x * 100)]
    == Log ["added one", "multiplied by 2", "multiplied by 100"] 800
