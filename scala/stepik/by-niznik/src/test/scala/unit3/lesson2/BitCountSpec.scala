package unit3.lesson2

import munit.FunSuite

class BitCountSpec extends FunSuite {
  test("sample") {
    assertEquals(BitCount.count(3), 2)
    assertEquals(BitCount.count(4), 1)
    assertEquals(BitCount.count(7), 3)
    assertEquals(BitCount.count(8), 1)
  }
}
