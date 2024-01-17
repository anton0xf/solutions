{- https://stepik.org/lesson/30723/step/5?unit=11811
3.2.5. Монада Cont -}

newtype Cont r a = Cont { runCont :: (a -> r) -> r }

evalCont :: Cont r r -> r
evalCont m = runCont m id

instance Functor (Cont r) where
  fmap :: (a -> b) -> Cont r a -> Cont r b
  -- fmap f (Cont cx) = Cont $ \c -> cx (\x -> c (f x))
  fmap f (Cont cx) = Cont $ \c -> cx (c . f)
  -- fmap f = Cont . (\h c -> h (c . f)) . runCont
  -- fmap f = Cont . (. (. f)) . runCont

instance Applicative (Cont r) where
  pure :: a -> Cont r a
  pure x = Cont ($ x)

  (<*>) :: Cont r (a -> b) -> Cont r a -> Cont r b
  -- (Cont cf) <*> (Cont cx) = Cont $ \yr -> cf (\f -> cx (\x -> yr $ f x))
  (Cont cf) <*> (Cont cx) = Cont $ \yr -> cf (\f -> cx (yr . f))
  -- (Cont cf) <*> (Cont cx) = Cont $ \yr -> cf (cx . (yr .))
  -- (Cont cf) <*> (Cont cx) = Cont $ cf . (cx .) . (.)

instance Monad (Cont r) where
  (>>=) :: Cont r a -> (a -> Cont r b) -> Cont r b
  -- (Cont cx) >>= k = Cont $ \yr -> cx $ \x -> runCont (k x) $ \y -> yr y
  (Cont cx) >>= k = Cont $ \yr -> cx $ \x -> runCont (k x) yr

square :: Int -> Cont r Int
square x = return $ x^2

add :: Int -> Int -> Cont r Int
add x y = return $ x + y

combTest :: Bool
combTest = evalCont (add 1 2 >>= square) == 9
  && evalCont (square 2 >>= add 3 >>= add 5) == 12

sumSquares :: Int -> Int -> Cont r Int
sumSquares x y = do
  x2 <- square x
  y2 <- square y
  add x2 y2

sumSquaresTest :: Bool
sumSquaresTest = evalCont (sumSquares 3 4) == 25

test :: Bool
test = combTest && sumSquaresTest
