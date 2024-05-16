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
  test("map") {
    val dict = DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(dict.map(_ + "_"), DictEx(ADictItem(1, "asdf_"), ADictItem(2, "qq_")))
  }
  test("prepend") {
    val dict: DictEx[TDictItem] = DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    val actual: DictEx[DictItem] = ADictItem(3, "aa") +: dict
    val expected: DictEx[DictItem] = DictEx(ADictItem(3, "aa"), TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(actual, expected)
  }
}
