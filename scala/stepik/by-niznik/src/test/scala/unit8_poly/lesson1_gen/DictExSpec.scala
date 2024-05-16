package unit8_poly.lesson1_gen

import munit.FunSuite

class DictExSpec extends FunSuite {
  test("head A") {
    val dict = DictEx(ADictItem(1, "asdf"), ADictItem(2, "qq"))
    assertEquals(dict.head, ADictItem(1, "asdf"))
  }
  test("head T") {
    val dict = DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(dict.head, TDictItem(1, "asdf"))
  }
}
