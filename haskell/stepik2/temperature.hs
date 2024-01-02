{- https://stepik.org/lesson/31555/step/8?unit=11808
2.3.8. Законы и свойства класса Traversable

Расширьте интерфейс для работы с температурами из предыдущего видео Кельвинами -}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
newtype Temperature a = Temperature Double
  deriving (Num, Show, Eq, Fractional)

data Celsius
data Fahrenheit 

comfortTemperature :: Temperature Celsius
comfortTemperature = Temperature 23

c2f :: Temperature Celsius -> Temperature Fahrenheit
c2f (Temperature c) = Temperature (1.8 * c + 32)

{- и реализуйте функцию k2c -}
data Kelvin

k2c :: Temperature Kelvin -> Temperature Celsius
k2c (Temperature c) = Temperature $ c - 273.15

{- обеспечивающую следующее поведение -}

k2cTest :: Bool
k2cTest = k2c 0 == Temperature (-273.15)
  && k2c 273.15 == Temperature 0.0

test :: Bool
test = k2cTest
