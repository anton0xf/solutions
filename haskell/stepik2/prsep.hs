{- https://stepik.org/lesson/30721/step/7?unit=11244
2.5.7. Классы типов Alternative и MonadPlus -}

import Data.Bifunctor
import Control.Applicative

{- Реализуем улучшенную версию парсера PrsE -}

newtype PrsEP a = PrsEP { runPrsEP :: Int -> String -> (Int, Either String (a, String)) }

{- Этот парсер получил дополнительный целочисленный параметр в аргументе
и в возвращаемом значении. С помощью этого параметра мы сможем отслеживать
и передвигать текущую позицию в разбираемой строке
и сообщать о ней пользователю в случае ошибки: -}

charEP :: Char -> PrsEP Char
charEP c = satisfyEP (== c)

charEPTest :: Bool
charEPTest = runPrsEP (charEP 'A') 0 "ABC" == (1, Right ('A', "BC"))
  && runPrsEP (charEP 'A') 41 "BCD" == (42, Left "pos 42: unexpected B")
  && runPrsEP (charEP 'A') 41 "" == (42, Left "pos 42: unexpected end of input")

{- Вспомогательная функция parseEP дает возможность вызывать парсер
более удобным образом по сравнению с runPrsEP, скрывая технические детали: -}

parseEP :: PrsEP a -> String -> Either String (a, String)
parseEP p  = snd . runPrsEP p 0

parseEPTest :: Bool
parseEPTest = parseEP (charEP 'A') "ABC" == Right ('A', "BC")
  && parseEP (charEP 'A') "BCD" == Left "pos 1: unexpected B"
  && parseEP (charEP 'A') "" == Left "pos 1: unexpected end of input"

{- Реализуйте функцию satisfyEP, обеспечивающую описанное выше поведение. -}

satisfyEP :: (Char -> Bool) -> PrsEP Char
satisfyEP pred = PrsEP p
  where p pos "" = let pos' = pos + 1
          in (pos', Left $ "pos " ++ show pos' ++ ": unexpected end of input")
        p pos (ch : str) = let pos' = pos + 1
          in (pos',
              if pred ch
              then Right (ch, str)
              else Left $ "pos " ++ show pos' ++ ": unexpected " ++ [ch])

{- https://stepik.org/lesson/30721/step/8?unit=11244
2.5.8. Классы типов Alternative и MonadPlus
Сделайте парсер PrsEP представителем классов типов Functor и Applicative,
обеспечив следующее поведение -}

functorTest :: Bool
functorTest = runPrsEP (pure 42) 0 "ABCDEFG" == (0, Right (42, "ABCDEFG"))
  && runPrsEP testP 0 "ABCDE" == (3, Right (('A', 'C'), "DE"))
  && parseEP testP "BCDE" == Left "pos 2: unexpected C"
  && parseEP testP "" == Left "pos 1: unexpected end of input"
  && parseEP testP "B" == Left "pos 2: unexpected end of input"

anyEP :: PrsEP Char
anyEP = satisfyEP (const True)

testP :: PrsEP (Char, Char)
testP = (,) <$> anyEP <* charEP 'B' <*> anyEP

instance Functor PrsEP where
  fmap :: (a -> b) -> PrsEP a -> PrsEP b
  -- fmap f (PrsEP px) = PrsEP p
  --   where p pos str = case px pos str of
  --           (pos1, Right (x, str1)) -> (pos1, Right (f x, str1))
  --           (pos1, Left err) -> (pos1, Left err)
  fmap f (PrsEP px) = PrsEP $ \pos str -> (fmap . first) f <$> px pos str
  -- fmap f (PrsEP px) = PrsEP $ ((fmap . fmap . first) f .) . px


instance Applicative PrsEP where
  pure :: a -> PrsEP a
  pure x = PrsEP $ \pos str -> (pos, Right (x, str))
  -- pure x = PrsEP $ (second (Right . (x,)) .) . (,)

  (<*>) :: PrsEP (a -> b) -> PrsEP a -> PrsEP b
  -- (PrsEP pf) <*> (PrsEP px) = PrsEP p
  --   where p pos str = case pf pos str of
  --           (pos1, Left err) -> (pos1, Left err)
  --           (pos1, Right (f, str1)) -> case px pos1 str1 of
  --             (pos2, Left err) -> (pos2, Left err)
  --             (pos2, Right (x, str2)) -> (pos2, Right (f x, str2))
  (PrsEP pf) <*> (PrsEP px) = PrsEP p
    where p pos str = case pf pos str of
            (pos1, Left err) -> (pos1, Left err)
            (pos1, Right (f, str1)) -> fmap (first f) <$> px pos1 str1

{- https://stepik.org/lesson/30721/step/9?unit=11244
2.5.9. Классы типов Alternative и MonadPlus
Сделайте парсер PrsEP представителем класса типов Alternative, обеспечив следующее поведение
для пары неудачных альтернатив: сообщение об ошибке возвращается из той альтернативы,
которой удалось распарсить входную строку глубже. -}

alternativeTest :: Bool
alternativeTest = runPrsEP (empty :: PrsEP ()) 0 "ABCDEFG" == (0, Left "pos 0: empty alternative")
  && parseEP (tripleP "ABC" <|> tripleP "ADC") "ABE" == Left "pos 3: unexpected E"
  && parseEP (tripleP "ABC" <|> tripleP "ADC") "ADE" == Left "pos 3: unexpected E"
  && parseEP (tripleP "ABC" <|> tripleP "ADC") "AEF" == Left "pos 2: unexpected E"

tripleP :: [Char] -> PrsEP [Char]
tripleP [a, b, c] = (\x y z -> [x,y,z]) <$> charEP a <*> charEP b <*>  charEP c

instance Alternative PrsEP where
  empty :: PrsEP a
  empty = PrsEP $ \pos str -> (pos, Left $ "pos " ++ show pos ++ ": empty alternative")

  (<|>) :: PrsEP a -> PrsEP a -> PrsEP a
  (PrsEP p1) <|> (PrsEP p2) = PrsEP $ \pos str -> case p1 pos str of
    (pos1, Left err1) -> case p2 pos str of
      (pos2, Left err2) -> if pos1 > pos2
                           then (pos1, Left err1)
                           else (pos2, Left err2)
      res -> res
    res -> res

test :: Bool
test = charEPTest && parseEPTest && functorTest && alternativeTest
