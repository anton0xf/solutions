package part2_start

import munit.FunSuite

class CombinatorsTest extends FunSuite {
  import Combinators._

  def f: Int => Int => Int = curry[Int, Int, Int](_ << _)

  test("curry") {
    assertEquals(f(1)(5), 32)
    assertEquals(f(2)(3), 16)
  }

  test("uncurry") {
    def uf: (Int, Int) => Int = uncurry[Int, Int, Int](f)
    assertEquals(uf(1, 5), 32)
    assertEquals(uf(2, 3), 16)
  }
}
