//> using target.scope test
import part4.Step_4_8_2._

class Step_4_8_2_test extends munit.FunSuite {
  test("compare") {
    assertEquals(compare("1.0.2.03", "1.1.0"), -1)
    assertEquals(compare("2.1", "2.01"), 0)
    assertEquals(compare("3.0", "3.0.0.0"), 0)
    assertEquals(compare("4", "4.0.0.1"), -1)
    assertEquals(compare("4.0.1", "4.0.0.1"), 1)
  }
}
