package unit5.lesson3

import munit.FunSuite

class PartialLogSpec extends FunSuite {
  test("sample") {
    assertEquals(PartialLog.log.isDefinedAt(-1.0), false)
    assertEquals(PartialLog.log.isDefinedAt(0.0), false)
    assertEquals(PartialLog.log.isDefinedAt(1.0), true)
    assertEqualsDouble(PartialLog.log(2.71), 1.0, 1e-2)
  }
}
