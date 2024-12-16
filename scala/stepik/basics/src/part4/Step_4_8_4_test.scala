//> using target.scope test
package part4

import Step_4_8_4._

class Step_4_8_4_test extends munit.FunSuite {
  test(""){
    assertEquals(countChars("None"), Map('n' -> 2, 'o' -> 1, 'e' -> 1))
  }
}