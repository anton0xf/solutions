{- https://stepik.org/lesson/30425/step/4?unit=11042
1.4.4. Аппликативный парсер своими руками -}

import Data.Char
import Data.Maybe
import Data.Bifunctor
import Control.Applicative

{- Предположим, тип парсера определен следующим образом: -}

newtype Prs a = Prs { runPrs :: String -> Maybe (a, String) }

{- Сделайте этот парсер представителем класса типов Functor.
Реализуйте также парсер anyChr :: Prs Char, удачно разбирающий
и возвращающий любой первый символ любой непустой входной строки. -}

instance Functor Prs where
  fmap :: (a -> b) -> Prs a -> Prs b
  fmap f p = Prs $ fmap (first f) . runPrs p

anyChr :: Prs Char
anyChr = Prs p where
  p "" = Nothing
  p (c : cs) = Just (c, cs)

testFunctor :: Bool
testFunctor = runPrs anyChr "ABC" == Just ('A',"BC")
  && isNothing (runPrs anyChr "")
  && runPrs (digitToInt <$> anyChr) "BCD" == Just (11,"CD")

{- https://stepik.org/lesson/30425/step/6?unit=11042
1.4.6. Аппликативный парсер своими руками

Сделайте парсер аппликативным функтором с естественной для парсера семантикой -}

instance Applicative Prs where
  pure :: a -> Prs a
  pure x = Prs $ \s -> Just (x, s)

  (<*>) :: Prs (a -> b) -> Prs a -> Prs b
  (Prs pf) <*> (Prs px) = Prs $ \s -> do
    (f, s1) <- pf s
    (x, s2) <- px s1
    return (f x, s2)

testApp :: Bool
testApp = runPrs ((,,) <$> anyChr <*> anyChr <*> anyChr) "ABCDE" == Just (('A','B','C'),"DE")
  && runPrs (anyChr *> anyChr) "ABCDE" == Just ('B',"CDE")

{- https://stepik.org/lesson/30425/step/12?unit=11042
Сделайте парсер представителем класса типов Alternative с естественной для парсера семантикой
-}

instance Alternative Prs where
  empty :: Prs a
  empty = Prs $ const Nothing
  
  (<|>) :: Prs a -> Prs a -> Prs a
  (Prs p1) <|> (Prs p2) = Prs $ \s -> p1 s <|> p2 s

satisfy :: (Char -> Bool) -> Prs Char
satisfy pred = Prs p where
  p "" = Nothing
  p (c:s) = if pred c then Just (c, s) else Nothing

char :: Char -> Prs Char
char c = satisfy (== c)

testAlt :: Bool
testAlt = runPrs (char 'A' <|> char 'B') "ABC" == Just ('A',"BC")
  && runPrs (char 'A' <|> char 'B') "BCD" == Just ('B',"CD")
  && isNothing (runPrs (char 'A' <|> char 'B') "CDE")

test :: Bool
test = testFunctor && testApp && testAlt
