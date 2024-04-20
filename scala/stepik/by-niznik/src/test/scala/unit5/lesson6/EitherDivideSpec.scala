package unit5.lesson6

import munit.FunSuite

class EitherDivideSpec extends FunSuite {
  import EitherDivide._

  test("divide") {
    assertEquals(divide((1, 10))((2, 10)), Right((1,2)))

    assertEquals(divide(1, 0)(1, 2), Left("Zero divisor"))
    assertEquals(divide(1, 2)(1, 0), Left("Zero divisor"))
    assertEquals(divide(1, 2)(0, 2), Left("Zero divisor"))

    assertEquals(divide(3, 4)(1, 10), Left("Improper result"))
    assertEquals(divide(1, 2)(1, 2), Left("Improper result"))

    assertEquals(divide(2, 1)(1, 7), Left("Invalid input"))
    assertEquals(divide(1, 2)(7, 1), Left("Invalid input"))
    assertEquals(divide(1, 1)(2, 2), Left("Invalid input"))
    assertEquals(divide(2, 1)(3, 1), Left("Invalid input"))

    assertEquals(divide(1, 2)(2, 3), Right((3,4)))
    assertEquals(divide(-1, 2)(2, 3), Right((-3,4)))
    assertEquals(divide(1, -2)(2, 3), Right((3, -4)))
    assertEquals(divide(1, 2)(-2, 3), Right((3, -4)))
    assertEquals(divide(1, 2)(2, -3), Right((-3, 4)))
  }
}
