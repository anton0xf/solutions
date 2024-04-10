package unit3.lesson3

import munit._

class StringsSpec extends FunSuite {
  test("sample") {
    assertEquals(Strings.isCapital("Scala", 0), true)
    assertEquals(Strings.isCapital("Scala", 1), false)
    assertEquals(Strings.isCapital("ABZ", 0), true)
    assertEquals(Strings.isCapital("ABZ", 1), true)
    assertEquals(Strings.isCapital("ABZ", 2), true)
    assertEquals(Strings.isCapital("abz", 0), false)
    assertEquals(Strings.isCapital("abz", 1), false)
    assertEquals(Strings.isCapital("abz", 2), false)

    assertEquals(Strings.isCapital("@[", 0), false)
    assertEquals(Strings.isCapital("@[", 1), false)
  }
}
