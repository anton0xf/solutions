package unit8_poly.lesson4_implicit

import munit.FunSuite

class MonoidExSpec extends FunSuite {
  import MonoidEx._

  test("concatAll"){
    assertEquals(concatAll(List()), "")
    assertEquals(concatAll(List("asdf")), "asdf")
    assertEquals(concatAll(List("ab", "c", "d")), "abcd")
  }

  test("sumAll"){
    assertEquals(sumAll(List()), 0)
    assertEquals(sumAll(List(5)), 5)
    assertEquals(sumAll(List(1, 2, 3)), 6)
  }

  test("forAll"){
    assertEquals(forAll(List()), true)
    assertEquals(forAll(List(true)), true)
    assertEquals(forAll(List(false)), false)
    assertEquals(forAll(List(true, true, true)), true)
    assertEquals(forAll(List(true, false, true)), false)
  }
}
