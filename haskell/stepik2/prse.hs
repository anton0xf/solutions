{- https://stepik.org/lesson/30425/step/8?unit=11042
1.4 Аппликативный парсер своими руками -}

newtype PrsE a = PrsE { runPrsE :: String -> Either String (a, String) }

satisfyE :: (Char -> Bool) -> PrsE Char
satisfyE pred = PrsE p where
  p "" = Left "unexpected end of input"
  p (c:cs) = if pred c then Right (c, cs) else Left ("unexpected " ++ [c])

charE :: Char -> PrsE Char
charE c = satisfyE (== c)

charETest :: Bool
charETest = runPrsE (charE 'A') "ABC" == Right ('A',"BC")
  && runPrsE (charE 'A') "BCD" == Left "unexpected B"
  &&  runPrsE (charE 'A') "" == Left "unexpected end of input"

{- https://stepik.org/lesson/30425/step/9?unit=11042
Сделайте парсер из предыдущей задачи функтором и аппликативным функтором -}

first :: (a -> b) -> (a, c) -> (b, c)
first f (x, y) = (f x, y)

instance Functor PrsE where
  fmap :: (a -> b) -> PrsE a -> PrsE b
  fmap f p = PrsE np where
    np e = fmap (first f) (runPrsE p e)

instance Applicative PrsE where
  pure :: a -> PrsE a
  pure x = PrsE $ \s -> Right (x, s)
  
  (<*>) :: PrsE (a -> b) -> PrsE a -> PrsE b
  (PrsE pf) <*> (PrsE px) = PrsE p where
    p s = do
      (f, s1) <- pf s
      (x, s2) <- px s1
      return (f x, s2)

testApp :: Bool
testApp = let anyE = satisfyE (const True)
          in runPrsE ((,) <$> anyE <* charE 'B' <*> anyE) "ABCDE" == Right (('A','C'),"DE")
             && runPrsE ((,) <$> anyE <* charE 'C' <*> anyE) "ABCDE" == Left "unexpected B"
             && runPrsE ((,) <$> anyE <* charE 'B' <*> anyE) "AB" == Left "unexpected end of input"

{- https://stepik.org/lesson/28881/step/7?unit=9913
2.4.7. Связь классов Monad и Applicative
Сделайте парсер PrsE из первого модуля курса представителем класса типов Monad -}

instance Monad PrsE where
  (>>=) :: PrsE a -> (a -> PrsE b) -> PrsE b
  (PrsE px) >>= k = PrsE p where
    p s = do
      (x, s1) <- px s
      let (PrsE py) = k x
      py s1

monadTest :: Bool
monadTest = runPrsE (do {a <- charE 'A'; b <- charE 'B'; return (a,b)}) "ABC"
      == Right (('A','B'),"C")
  && runPrsE (do {a <- charE 'A'; b <- charE 'B'; return (a,b)}) "ACD" == Left "unexpected C"
  && runPrsE (do {a <- charE 'A'; b <- charE 'B'; return (a,b)}) "BCD" == Left "unexpected B"

test :: Bool
test = charETest && testApp && monadTest
