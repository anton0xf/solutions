//> using target.scope test
import part4.Step_4_8_3._

class Step_4_8_3_test extends munit.FunSuite {
  test("duplicate") {
    assertEquals(duplicate(List(1, 2, 3), 2), List(1, 1, 2, 2, 3, 3))
    assertEquals(duplicate(List(1.0, 2.4, 3.6), 2), List(1.0, 1.0, 2.4, 2.4, 3.6, 3.6))
  }
}
