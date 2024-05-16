package unit8_poly.lesson1_gen

import munit.FunSuite

class DictExSpec extends FunSuite {
  test("head A") {
    val dict: DictEx[Int, ADictItem[Int]] = DictEx(ADictItem(1, "asdf"), ADictItem(2, "qq"))
    assertEquals(dict.head, ADictItem(1, "asdf"))
  }
  test("head T") {
    val dict: DictEx[Int, TDictItem[Int]] = DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(dict.head, TDictItem(1, "asdf"))
  }
  test("head AT") {
    val dict: DictEx[Int, DictItem[Int]] = DictEx(ADictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(dict.head, ADictItem(1, "asdf"))
  }
  test("map") {
    val dict: DictEx[Int, TDictItem[Int]] = DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    val expected: DictEx[Int, ADictItem[Int]] = DictEx(ADictItem(1, "asdf_"), ADictItem(2, "qq_"))
    assertEquals(dict.map(_ + "_"), expected)
  }
  test("prepend") {
    val dict: DictEx[Int, TDictItem[Int]] = DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    val actual: DictEx[Int, DictItem[Int]] = ADictItem(3, "aa") +: dict
    val expected: DictEx[Int, DictItem[Int]] =
      DictEx(ADictItem(3, "aa"), TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(actual, expected)
  }
}
