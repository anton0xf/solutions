package unit3.lesson2

class CrispsSpec extends munit.FunSuite {
    test("sample") {
        assertEquals(Crisps.crispsWeight(90.0, 0.9, 0.1), BigDecimal("10.00000"))
    }
}