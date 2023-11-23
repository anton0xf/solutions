{- https://stepik.org/lesson/28880/step/4?unit=9912
1.1 Определение аппликативного функтора step 4

В модуле Data.Functor определен оператор <$>, являющийся инфиксным аналогом функции fmap:

GHCi> :info <$>
(<$>) :: Functor f => (a -> b) -> f a -> f b
        -- Defined in `Data.Functor'
infixl 4 <$>

В выражении succ <$> "abc" этот оператор имеет тип (Char -> Char) -> [Char] -> [Char].
Какой тип имеет первое (левое) вхождение этого оператора в выражении succ <$> succ <$> "abc"?
-}

succ'succ :: Char -> Char
succ'succ = f succ succ where
  f :: (Char -> Char) -> (Char -> Char) -> Char -> Char
  f = (<$>)

test = (succ'succ <$> "abc") == "cde"
