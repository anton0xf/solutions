package part2_start

import munit.FunSuite

class CombinatorsTest extends FunSuite {
  import Combinators._

  test("curry") {
    def f: Int => Int => Int = curry[Int, Int, Int](_ << _)
    assertEquals(f(1)(5), 32)
    assertEquals(f(2)(3), 16)
  }

  test("uncurry") {
    def f: Int => Int => Int = x => y => x << y
    def uf: (Int, Int) => Int = uncurry[Int, Int, Int](f)
    assertEquals(uf(1, 5), 32)
    assertEquals(uf(2, 3), 16)
  }

  test("compose") {
    def f: String => String = _ + "b"
    def g: String => String = _ + "c"
    assertEquals(compose(g, f)("a"), "abc")
  }
}
