{- https://stepik.org/lesson/30721/step/7?unit=11244
2.5.7. Классы типов Alternative и MonadPlus -}

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

test :: Bool
test = charEPTest && parseEPTest
