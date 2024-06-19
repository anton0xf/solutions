package part2_start

import munit.FunSuite
class FibTest extends FunSuite {
  import Fib._
  test("fac") {
    assertEquals((0 to 5).map(fac), Vector(1, 1, 2, 6, 24, 120))
  }
  test("fib") {
    assertEquals((0 to 7).map(fib), Vector(0, 1, 1, 2, 3, 5, 8, 13))
  }
}
