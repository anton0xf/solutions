module SumAndCount where

import Data.Char

sum'n'count :: Integer -> (Integer, Integer)
sum'n'count x = (s, n)
  where
    str = show $ abs x
    ds = map digitToInt str
    s = fromIntegral $ sum ds
    n = fromIntegral $ length str

main = do
  print $ sum'n'count (-39)
