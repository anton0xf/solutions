def fix(f: (=> Int => Int) => Int => Int): Int => Int = f(fix(f))

def sumTo (recur: => Int => Int) (n: Int): Int =
  if (n == 0) 0 else n + recur(n - 1)

fix(sumTo)(0)
fix(sumTo)(1)
fix(sumTo)(2)
fix(sumTo)(3)
fix(sumTo)(4)
fix(sumTo)(42)
