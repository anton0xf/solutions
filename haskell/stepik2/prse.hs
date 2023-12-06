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


test :: Bool
test = charETest
