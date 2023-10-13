{-
$ rm -rf build bin \
  && mkdir -p build bin \
  && ghc fib.hs -hidir build -odir build -o bin/fib \
  && time ./bin/fib +RTS -s

see https://stepik.org/lesson/8413/step/10?discussion=165416&reply=166477&unit=1552
-}

fib :: Integer -> Integer
fib 0 = 0
fib 1 = 1
fib n = fib (n-2) + fib (n-1)

fib' :: Integer -> Integer
fib' n = let iter a b 0 = a
             iter a b n = iter b (a + b) (n - 1)
             in iter 0 1 n

main = do print $ show $ fib 30
