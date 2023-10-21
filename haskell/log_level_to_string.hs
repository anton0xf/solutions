{- https://stepik.org/lesson/5431/step/3?unit=1132

4.3 Синтаксис записей step 3

Определите тип записи, который хранит элементы лога.
Имя конструктора должно совпадать с именем типа, и запись должна содержать три поля:

    timestamp — время, когда произошло событие (типа UTCTime);
    logLevel — уровень события (типа LogLevel);
    message — сообщение об ошибке (типа String).

Определите функцию logLevelToString, возвращающую текстуальное представление типа LogLevel, и функцию logEntryToString, возвращающую текстуальное представление записи в виде:

<время>: <уровень>: <сообщение>

Для преобразование типа UTCTime в строку используйте функцию timeToString.
-}

import Data.Time.Calendar
import Data.Time.Clock
import Data.Time.Format
-- import System.Locale
import Data.Time.Format.ISO8601
import Data.List

timeToString :: UTCTime -> String
timeToString = formatTime defaultTimeLocale "%a %d %T"

data LogLevel = Error | Warning | Info deriving Show

data LogEntry = LogEntry {timestamp :: UTCTime, logLevel :: LogLevel, message :: String}

logLevelToString :: LogLevel -> String
logLevelToString = show

logEntryToString :: LogEntry -> String
logEntryToString (LogEntry ts lvl msg)
  = intercalate " : " [timeToString ts, show lvl, msg]

someDay = UTCTime d 0
  where (Just d) = fromGregorianValid 2008 10 22

{- logEntryToString $ LogEntry someDay Warning "Hello!"
"Wed 22 00:00:00 : Warning : Hello!" -}
