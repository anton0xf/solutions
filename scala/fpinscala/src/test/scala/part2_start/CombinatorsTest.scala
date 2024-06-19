package part2_start

import munit.FunSuite

class CombinatorsTest extends FunSuite {
  import Combinators._

  test("curry") {
    def f = curry[Int, Int, Int](_ << _)
    assertEquals(f(1)(5), 32)
    assertEquals(f(2)(3), 16)
  }
}
