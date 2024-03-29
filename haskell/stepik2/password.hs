{- https://stepik.org/lesson/38580/step/8?unit=20505
4.3.8. Трансформер ExceptT
Следующий код -}

import Data.Foldable
import Control.Monad 
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except hiding (except)
import Data.Char (isNumber, isPunctuation)

askPassword0 :: MaybeT IO ()
askPassword0 = do
  liftIO $ putStrLn "Enter your new password:"
  value <- msum $ repeat getValidPassword0
  liftIO $ putStrLn "Storing in database..."

getValidPassword0 :: MaybeT IO String
getValidPassword0 = do
  s <- liftIO getLine
  guard (isValid0 s)
  return s

isValid0 :: String -> Bool
isValid0 s = length s >= 8
            && any isNumber s
            && any isPunctuation s

{- используя трансформер MaybeT и свойства функции msum, отвергает ввод пользовательского пароля,
до тех пор пока он не станет удовлетворять заданным критериям. Это можно проверить,
вызывая его в интерпретаторе 

GHCi> runMaybeT askPassword0

Используя пользовательский тип ошибки и трансформер ExceptT вместо MaybeT,
модифицируйте приведенный выше код так, чтобы он выдавал пользователю сообщение о причине,
по которой пароль отвергнут. -}

newtype PwdError = PwdError String
  deriving (Eq, Show)

instance Semigroup PwdError where
  (<>) :: PwdError -> PwdError -> PwdError
  (PwdError s1) <> (PwdError s2) = PwdError $ s1 ++ s2

instance Monoid PwdError where
  mempty :: PwdError
  mempty = PwdError ""

type PwdErrorIOMonad = ExceptT PwdError IO

askPassword :: PwdErrorIOMonad ()
askPassword = do
  liftIO $ putStrLn "Enter your new password:"
  value <- msum $ repeat getValidPassword
  liftIO $ putStrLn "Storing in database..."
  
getValidPassword :: PwdErrorIOMonad String
getValidPassword = do
      s <- liftIO getLine
      validatePwd s
      return s
  `catchE` \e@(PwdError msg) -> do
      liftIO $ putStrLn msg
      throwE e

validatePwd :: String -> PwdErrorIOMonad ()
validatePwd s = except check
  where check | length s < 8 = err "password is too short!"
              | not $ any isNumber s = err "password must contain some digits!"
              | not $ any isPunctuation s = err "password must contain some punctuation!"
              | otherwise = Right ()
        err = Left . PwdError . ("Incorrect input: " ++)

except :: Monad m => Either e a -> ExceptT e m a
except x = ExceptT $ return x

{- Ожидаемое поведение:

GHCi> runExceptT askPassword
Enter your new password:
qwerty
Incorrect input: password is too short!
qwertyuiop
Incorrect input: password must contain some digits!
qwertyuiop123
Incorrect input: password must contain some punctuation!
qwertyuiop123!!!
Storing in database...
GHCi>

-}
