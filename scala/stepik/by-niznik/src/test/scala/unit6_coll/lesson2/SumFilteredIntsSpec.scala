package unit6_coll.lesson2

import munit.FunSuite

class SumFilteredIntsSpec extends FunSuite {
  test("example") {
    assertEquals(SumFilteredInts.filteredSum(Seq("28", "40", "9", "61", "END", "23", "12", "34")), 202)
  }
}
