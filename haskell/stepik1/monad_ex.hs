{- https://stepik.org/lesson/8441/step/3?unit=1576
5.6 Монада Reader - step 3

Не используя интерпретатор, вычислите значение следующего выражения:

return 2 >>= (+) >>= (*) $ 4
-}
-- return :: Monad m => a -> m a
-- (>>=) :: Monad m => m a -> (a -> m b) -> m b

-- return a >>= k                  =  k a
-- m        >>= return             =  m
-- m        >>= (\x -> k x >>= h)  =  (m >>= k) >>= h

v0 = return 2 >>= (+) >>= (*) $ 4

-- (+) :: Num -> Num -> Num  == a -> m b
-- a == Num
-- m b == Num -> Num

v1 = (2 +) >>= (*) $ 4

-- m a -> (a -> m b) -> m b
-- (Num -> Num) -> (Num -> Num -> Num) -> Num -> Num
-- m >>= k == \e -> k (m e) e
-- m = (2 +)
-- k = (*)
v2 = (\e -> (2 + e) * e) 4

v3 = (2 + 4) * 4 -- 24

