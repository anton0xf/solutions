package part2_start

import scala.annotation.tailrec

/*
exercise 2.1.
Write a recursive function to get the nth Fibonacci number (http://mng.bz/C29s).
The first two Fibonacci numbers are 0 and 1. The nth number is always the
sum of the previous two—the sequence begins 0, 1, 1, 2, 3, 5.
Your definition should use a local tail-recursive function.
 */
object Fib {
  def fac(n: Int): Int = {
    @tailrec
    def go(n: Int, acc: Int): Int = if (n == 0) acc else go(n - 1, acc * n)
    go(n, 1)
  }

  def fib(n: Int): Int = {
    @tailrec
    def go(a: Int, b: Int, m: Int): Int = if (m == n) b else go(b, a + b, m + 1)
    if (n == 0) 0 else go(0, 1, 1)
  }
}
