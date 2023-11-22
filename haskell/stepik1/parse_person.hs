{- https://stepik.org/lesson/5746/step/9?unit=1256
4.4 Типы с параметрами step 9

Реализуйте функцию parsePerson, которая разбирает строки вида
> firstName = John\nlastName = Connor\nage = 30
и возвращает либо результат типа Person, либо ошибку типа Error.

* Строка, которая подается на вход, должна разбивать по символу '\n'
  на список строк, каждая из которых имеет вид X = Y.
  Если входная строка не имеет указанный вид, то функция должна возвращать ParsingError.
* Если указаны не все поля, то возвращается IncompleteDataError.
* Если в поле age указано не число, то возвращается IncorrectDataError str,
  где str — содержимое поля age.
* Если в строке присутствуют лишние поля, то они игнорируются.
-}

import Data.List (stripPrefix)
import Control.Arrow (first)
import Data.Maybe (isNothing, fromJust)
import Text.Read ( readMaybe )

-- https://hackage.haskell.org/package/extra-1.7.14/docs/src/Data.List.Extra.html#stripInfix
-- | Return the the string before and after the search string,
--   or 'Nothing' if the search string is not present.
--
-- Examples:
-- > stripInfix "::" "a::b::c" == Just ("a", "b::c")
-- > stripInfix "/" "foobar"   == Nothing
stripInfix :: Eq a => [a] -> [a] -> Maybe ([a], [a])
stripInfix needle haystack | Just rest <- stripPrefix needle haystack = Just ([], rest)
stripInfix needle [] = Nothing
stripInfix needle (x:xs) = case stripInfix needle xs of
  Just (prefix, next) -> Just (x:prefix, next)
  Nothing -> Nothing

getKv :: [(String, String)] -> String -> Maybe String
getKv [] _ = Nothing
getKv ((k,v):kvs) key = if k == key then Just v else getKv kvs key

data Error = ParsingError | IncompleteDataError | IncorrectDataError String

data Person = Person { firstName :: String, lastName :: String, age :: Int }
  deriving Show

parsePerson :: String -> Either Error Person
parsePerson s = let
    mkvs = map (stripInfix " = ") $ lines s
    kvs = map fromJust mkvs
    get = getKv kvs
  in if any isNothing mkvs then Left ParsingError
     else case (get "firstName", get "lastName", get "age") of
       (Just fn, Just ln, Just ageStr) ->
         case readMaybe ageStr of
           Nothing -> Left $ IncorrectDataError ageStr
           Just ageVal -> Right Person {firstName=fn, lastName=ln, age=ageVal}
       _ -> Left IncompleteDataError
            
