import example.SqrtIter.*

isGoodEnough(0.1, 0.01)
isGoodEnough(0.01, 0.0001)
isGoodEnough(0.001, 0.000001)
isGoodEnough(1e-20, 1e-40)
isGoodEnough(1e-21, 1e-42)
isGoodEnough(1e20, 1e40+0.1)
isGoodEnough(1e50, 1e100) // false
