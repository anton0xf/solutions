{-
https://stepik.org/lesson/4985/step/6

It is continualtion of task https://stepik.org/lesson/4916/step/13?unit=1082
-}
data Result = Fail | Success

data SomeData = SomeData Int

doSomeWork :: SomeData -> (Result, Int)
doSomeWork (SomeData 0) = (Success, 0)
doSomeWork (SomeData n) = (Fail, n)

data Result' = Success' | Fail' Int

instance Show Result' where
    show Success' = "Success"
    show (Fail' n) = "Fail: " ++ show n

doSomeWork' :: SomeData -> Result'
doSomeWork' d = case doSomeWork d of
    (Success, _) -> Success'
    (Fail, n) -> Fail' n
