{- https://stepik.org/lesson/38581/step/5?unit=20506 -}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

{- 4.4.5. Неявный лифтинг
Предположим мы хотим реализовать следующую облегченную версию функтора,
используя многопараметрические классы типов: -}

class Functor' c e | c -> e where
  fmap' :: (e -> e) -> c -> c

{- Добавьте в определение этого класса типов необходимые функциональные зависимости и реализуйте
его представителей для списка и Maybe так, чтобы обеспечить работоспособность следующих вызовов -}

fmap'Test :: Bool
fmap'Test = fmap' succ "ABC" == "BCD"
  && fmap' (^2) (Just 42) == Just 1764

-- instance Functor' [a] a where
--   fmap' = map

-- instance Functor' (Maybe a) a where
--   fmap' = fmap

instance Functor f => Functor' (f a) a where
  fmap' = fmap

test :: Bool
test = fmap'Test
