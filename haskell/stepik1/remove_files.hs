{- https://stepik.org/lesson/8443/step/8?unit=1578
5.5 Монада IO step 8

В этом задании ваша программа должна попросить пользователя ввести любую
строку, а затем удалить все файлы в текущей директории, в именах которых
содержится эта строка, выдавая при этом соответствующие сообщения.

'Substring: '

Пользователь вводит любую строку:

Substring: hell

Затем программа удаляет из текущей директории файлы с введенной
подстрокой в названии. К примеру, если в текущей директории находились
файлы thesis.txt, kitten.jpg, hello.world, linux_in_nutshell.pdf,
то вывод будет таким:

Substring: hell
Removing file: hello.world
Removing file: linux_in_nutshell.pdf

Если же пользователь ничего не ввёл (просто нажал Enter),
следует ничего не удалять и сообщить об этом:

Substring: 
Canceled

Для получения списка файлов в текущей директории используйте функцию
getDirectoryContents, передавая ей в качестве аргумента строку, состоящую
из одной точки  ("."), что означает «текущая директория».
Для удаления файлов используйте функцию removeFile (считайте, что в
текущей директории нет поддиректорий — только простые файлы).
В выводимых сообщениях удаленные файлы должны быть перечислены в том же
порядке, в котором их возвращает функция getDirectoryContents.
-}
import System.IO
import System.Directory
import Data.List (isInfixOf)

rmFile file = do
  putStrLn $ "Removing file: " ++ file
  removeFile file

rmByInfix s = do
  files <- getDirectoryContents "."
  mapM_ rmFile $ filter (isInfixOf s) files

main' :: IO ()
main' = do
  putStr "Substring: "
  hFlush stdout
  s <- getLine
  if s == "" then putStrLn "Canceled"
    else rmByInfix s

-- main = main'
