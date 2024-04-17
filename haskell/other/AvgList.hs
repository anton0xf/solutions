module AvgList where

fillAvg :: (Fractional a) => [a] -> [a]
fillAvg xs =
  let
    (n, sum, res) = foldr iter (0, 0, []) xs
    iter x (n, sum, res) = (n + 1, sum + x, avg : res)
    avg = sum / n
  in res

