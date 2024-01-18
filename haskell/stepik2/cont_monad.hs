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

{- https://stepik.org/lesson/30723/step/9?unit=11811
3.2.9. Монада Cont
Возможность явно работать с продолжением обеспечивает доступ к очень гибкому управлению
исполнением. В этом задании вам предстоит реализовать вычисление, которое анализирует и
модифицирует значение, возвращаемое кодом, написанным после него.

В качестве примера рассмотрим следующую функцию: -}

addTens :: Int -> Checkpointed Int
addTens x1 checkpoint = do
  checkpoint x1
  let x2 = x1 + 10
  checkpoint x2     {- x2 = x1 + 10 -}
  let x3 = x2 + 10
  checkpoint x3     {- x3 = x1 + 20 -}
  let x4 = x3 + 10
  return x4         {- x4 = x1 + 30 -}

{- Эта функция принимает значение x1, совершает с ним последовательность операций
(несколько раз прибавляет 10) и после каждой операции «сохраняет» промежуточный результат.
При запуске такой функции используется дополнительный предикат, который является критерием
«корректности» результата, и в случае, если возвращенное функцией значение этому критерию
не удовлетворяет, вернется последнее удовлетворяющее ему значение из «сохраненных»: -}

addTensTest :: Bool
addTensTest = runCheckpointed (< 100) (addTens 1) == 31
  && runCheckpointed  (< 30) (addTens 1) == 21
  && runCheckpointed  (< 20) (addTens 1) == 11
  && runCheckpointed  (< 10) (addTens 1) == 1

{- (Если ни возвращенное, ни сохраненные значения не подходят, результатом должно быть первое
из сохраненных значений; если не было сохранено ни одного значения, то результатом должно быть
возвращенное значение.)

Обратите внимание на то, что функция checkpoint передается в Checkpointed вычисление как параметр,
поскольку её поведение зависит от предиката,
который будет известен только непосредственно при запуске. -}

type Checkpointed a = (a -> Cont a a) -> Cont a a

runCheckpointed :: (a -> Bool) -> Checkpointed a -> a
runCheckpointed pred cp = evalCont (cp checkpoint)
  where checkpoint x = Cont $ \c -> let v = c x
                                    in if pred v then v else x


test :: Bool
test = combTest && sumSquaresTest && addTensTest
