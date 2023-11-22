{- examples from https://habr.com/ru/articles/184722/ Тройка полезных монад
https://www.adit.io/posts/2013-06-10-three-useful-monads.html Three Useful Monads
by Aditya Bhargava 
-}
import Control.Monad.Reader

greeter :: Reader String String
greeter = do
    name <- ask
    return ("hello, " ++ name ++ "!")

-- (runReader greeter) "Anton"
-- => "hello, Anton!"

greeter2 :: Reader String String
greeter2 = do
    name <- ask
    lastName <- ask
    return ("hello, " ++ name ++ " " ++ lastName ++ "!")

constStr :: String -> String -> Reader Integer String
constStr c s = return $ s ++ c

space :: String -> Reader Integer String
space = constStr " "

askInt :: String -> Reader Integer String
askInt s = reader ((s ++) . show)

testReader :: Reader Integer String
testReader = constStr ">" "" >>= space >>= askInt >>= constStr " - " >>= askInt

-- (runReader testReader) 1
-- => "> 1 - 1"
