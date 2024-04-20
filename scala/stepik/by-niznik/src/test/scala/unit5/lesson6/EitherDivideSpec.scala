package unit5.lesson6

import munit.FunSuite

class EitherDivideSpec extends FunSuite {
  import EitherDivide._

  test("divide") {
    assertEquals(divide((1, 10))((2, 10)), Right((1,2)))
  }
}
