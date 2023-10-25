{- https://stepik.org/lesson/5746/step/12?unit=1256
4.4 Типы с параметрами step 12

Исправьте ошибку в приведенном коде.
-}

eitherToMaybe :: Either a b -> Maybe a
eitherToMaybe (Left a) = Just a
eitherToMaybe (Right _) = Nothing
