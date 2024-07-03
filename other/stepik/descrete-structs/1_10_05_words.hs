-- https://stepik.org/lesson/8169/step/5?unit=1385
import Data.List

-- m-letter alphabet
-- n-letter strings without k-letter substring s (without repeating letters)

nWords :: String -> Int -> [String]
nWords alphabet n = go n [""]
  where go 0 acc = acc
        go n acc = go (n-1) [ ch : s | s <- acc, ch <- alphabet]

-- length $ nWords "abc" 4
-- => 81 = 3^4

countNWordsWithout :: String -> Int -> String -> Int
countNWordsWithout alph n s = length $ filter (isInfixOf s) $ nWords alph n

-- countNWordsWithout "abc" 5 "abc"
-- => 27 = 3^2 * 3

-- countNWordsWithout "abc" 4 "ab"
-- => 26 = 3^2^3 - 1

-- countNWordsWithout "abc" 5 "ab"
-- => 99 = 3^3 * 4 - 3*3

-- 4-2 = 2
-- 3^2 * 3

