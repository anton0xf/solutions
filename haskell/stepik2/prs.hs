{- https://stepik.org/lesson/30425/step/4?unit=11042
1.4.4. Аппликативный парсер своими руками -}

import Data.Char

{- Предположим, тип парсера определен следующим образом: -}

newtype Prs a = Prs { runPrs :: String -> Maybe (a, String) }

{- Сделайте этот парсер представителем класса типов Functor.
Реализуйте также парсер anyChr :: Prs Char, удачно разбирающий
и возвращающий любой первый символ любой непустой входной строки. -}

instance Functor Prs where
  fmap :: (a -> b) -> Prs a -> Prs b
  -- fmap f p = Prs $ fmap (first f) (runPrs p)
  fmap f p = Prs $ fmap (\(x, s) -> (f x, s)) . runPrs p

anyChr :: Prs Char
anyChr = Prs p where
  p "" = Nothing
  p (c : cs) = Just (c, cs)

test :: Bool
test = runPrs anyChr "ABC" == Just ('A',"BC")
  && runPrs anyChr "" == Nothing
  && runPrs (digitToInt <$> anyChr) "BCD" == Just (11,"CD")

