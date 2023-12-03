{- https://stepik.org/lesson/30425/step/4?unit=11042
1.4.4. Аппликативный парсер своими руками -}

import Data.Char
import Data.Maybe
import Data.Bifunctor

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

test :: Bool
test = testFunctor && testApp
