{- https://stepik.org/lesson/30722/step/14?unit=11809
3.1.14. Монада Except -}

import Control.Monad.Trans.Except
import Data.List
import Data.Bifunctor
import Control.Monad

{- Стандартная семантика Except как аппликативного функтора и монады:
выполнять цепочку вычислений до первой ошибки.

Реализация представителей классов Alternative и MonadPlus наделяет эту монаду альтернативной☺
семантикой: попробовать несколько вычислений, вернуть результат первого успешного,
а в случае неудачи — все возникшие ошибки.

Довольно часто возникает необходимость сделать нечто среднее. К примеру, при проверке корректности
заполнения анкеты или при компиляции программы для общего успеха необходимо, чтобы ошибок совсем
не было, но в то же время, нам хотелось бы не останавливаться после первой же ошибки,
а продолжить проверку, чтобы отобразить сразу все проблемы. Except такой семантикой не обладает,
но никто не может помешать нам сделать свой тип данных (назовем его Validate), представители
которого будут обеспечивать требую семантику, позволяющую сохранить список всех произошедших
ошибок: -}

newtype Validate e a = Validate { getValidate :: Either [e] a }

{- Реализуйте функцию validateSum.
Эта функция практически ничем не отличается от уже реализованной ранее trySum (see try_read.hs),
если использовать функцию-адаптер collectE и представителей каких-нибудь классов
типов для Validate -}

data ReadError = EmptyInput | NoParse String
  deriving (Show, Eq)

tryRead :: Read a => String -> Except ReadError a
tryRead "" = throwE EmptyInput
tryRead str = case filter (null . snd) $ reads str of
  [] -> throwE $ NoParse str
  [(x, "")] -> return x

data SumError = SumError Int ReadError
  deriving (Show, Eq)

collectE :: Except e a -> Validate e a
collectE = Validate . first singleton . runExcept

instance Functor (Validate e) where
  fmap :: (a -> b) -> Validate e a -> Validate e b
  fmap f = Validate . second f . getValidate

instance Applicative (Validate e) where
  pure :: a -> Validate e a
  pure x = Validate $ Right x

  (<*>) :: Validate e (a -> b) -> Validate e a -> Validate e b
  (Validate ef) <*> (Validate ex) = Validate $ ap' ef ex
    where ap' (Right f) (Right x) = Right $ f x
          ap' (Left e1) (Left e2) = Left $ e1 ++ e2
          ap' (Left e1) _ = Left e1
          ap' _ (Left e2) = Left e2

validateSum :: [String] -> Validate SumError Integer
validateSum = fmap sum . zipWithM ((collectE .) . withExcept . SumError) [1..] . map tryRead

getValidateTest :: Bool
getValidateTest = getValidate (validateSum ["10", "20", "30"]) == Right 60
  && getValidate (validateSum ["10", "", "30", "oops"]) == Left [SumError 2 EmptyInput,
                                                                 SumError 4 (NoParse "oops")]

test :: Bool
test = getValidateTest
