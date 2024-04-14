val add1 : Int => Int = _ + 1
val calc42 = (f: Int => Int) => f(42)
calc42(add1)
def sumTo(n: Int): Int = if (n == 0) 0 else n + sumTo(n - 1)
calc42(sumTo)

//def fix(f: (Int => Int) => Int => Int)(n: Int): Int = {
//  f(f(x => ???))(n)
//}

def fix(f: (Int => Int) => Int => Int): Int => Int = {
    def res: Int => Int = f(res(_)) // not just f(res)
    res
}

//def fix(f: (Int => Int) => Int => Int): Int => Int = {
//  ((res: Int => Int) => f(x => res(x)))(x => fix(f)(x))
//}

((n: Int) => if (n == 0) 0 else ???)(0)

val sumTo2 = (recur: Int => Int) => (n: Int) =>
  if (n == 0) 0 else n + recur(n - 1)
fix(sumTo2)(0)
fix(sumTo2)(1)
fix(sumTo2)(2)
sumTo(3)
fix(sumTo2)(3)
sumTo(4)
fix(sumTo2)(4)

calc42(fix(recur => n => if (n == 0) 0 else n + recur(n - 1)))
