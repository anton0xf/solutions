package unit8_poly.lesson3_alias

import munit.FunSuite
import unit8_poly.lesson3_alias.Vect._

//noinspection NameBooleanParameters
class VectSpec extends FunSuite {
  test("StringVect") {
    val v = StringVect("abc")
    assertEquals(v.length, 3)
    assertEquals(v.get(0), 'a')
    assertEquals(v.get(1), 'b')
    assertEquals(v.get(2), 'c')
    assertEquals(v.set(1, 'd'), StringVect("adc"))
    assertEquals(toList(v), List('a', 'b', 'c'))
  }

  test("BoolVect8") {
    assertEquals(toBoolList(BoolVect8(4)), "00100000")
    assertEquals(toBoolList(BoolVect8(4).set(3, true)), "00110000")
    assertEquals(toBoolList(BoolVect8(4).set(8, true)), "00100000")
    assertEquals(toBoolList(BoolVect8(4).set(9999, true)), "00100000")
    assertEquals(toBoolList(BoolVect8(4).set(-1, true)), "00100000")
    assertEquals(BoolVect8(4).get(0), false)
    assertEquals(BoolVect8(4).get(1), false)
    assertEquals(BoolVect8(4).get(2), true)

    assertEquals(toBoolList(BoolVect8(3)), "11000000")
    assertEquals(BoolVect8(3).get(0), true)
    assertEquals(BoolVect8(3).get(1), true)
    assertEquals(BoolVect8(3).get(2), false)
    assertEquals(BoolVect8(3).get(3), false)
    assertEquals(BoolVect8(3).get(6), false)

    assertEquals(toBoolList(BoolVect8(1)), "10000000")
    assertEquals(toBoolList(BoolVect8(0)), "00000000")
    assertEquals(toBoolList(BoolVect8(-1)), "11111111")
    assertEquals(toBoolList(BoolVect8(-1).set(0, false)), "01111111")
    assertEquals(BoolVect8(-1).get(1), true)

    assertEquals(toBoolList(BoolVect8(-2)), "01111111")
  }
  
  test("BoolVect64") {
    assertEquals(toBoolList(BoolVect64(3L)), "1100000000000000000000000000000000000000000000000000000000000000")
    assertEquals(toBoolList(BoolVect64(4L)), "0010000000000000000000000000000000000000000000000000000000000000")
    assertEquals(toBoolList(BoolVect64(4L).set(3, true)), "0011000000000000000000000000000000000000000000000000000000000000")
    assertEquals(toBoolList(BoolVect64(4).set(64, true)), "0010000000000000000000000000000000000000000000000000000000000000")
    assertEquals(toBoolList(BoolVect64(4).set(9999, true)), "0010000000000000000000000000000000000000000000000000000000000000")
    assertEquals(toBoolList(BoolVect64(4).set(-1, true)), "0010000000000000000000000000000000000000000000000000000000000000")
  }
}
