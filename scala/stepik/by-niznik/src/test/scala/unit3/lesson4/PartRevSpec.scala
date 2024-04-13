package unit3.lesson4

import munit.FunSuite

class PartRevSpec extends FunSuite {
  test("sample") {
    assertEquals(PartRev.reversePart("abcd", 1, 2), "acbd")
    assertEquals(PartRev.reversePart("foobarbaz", 2, 6), "fobraboaz")
  }
}
