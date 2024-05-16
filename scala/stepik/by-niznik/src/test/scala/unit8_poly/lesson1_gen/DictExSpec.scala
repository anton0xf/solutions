package unit8_poly.lesson1_gen

import munit.FunSuite

class DictExSpec extends FunSuite {
  test("head A") {
    val dict: DictEx[Int, String, ADictItem[Int, String]] =
      DictEx(ADictItem(1, "asdf"), ADictItem(2, "qq"))
    assertEquals(dict.head, ADictItem(1, "asdf"))
  }

  test("head T") {
    val dict: DictEx[Int, String, TDictItem[Int, String]] =
      DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(dict.head, TDictItem(1, "asdf"))
  }

  test("head AT") {
    val dict: DictEx[Int, String, DictItem[Int, String]] =
      DictEx(ADictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(dict.head, ADictItem(1, "asdf"))
  }

  test("map") {
    val dict: DictEx[Int, String, TDictItem[Int, String]] =
      DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    val expected: DictEx[Int, String, ADictItem[Int, String]] =
      DictEx(ADictItem(1, "asdf_"), ADictItem(2, "qq_"))
    assertEquals(dict.map(_ + "_"), expected)
  }

  test("map to other type") {
    val dict: DictEx[Int, String, TDictItem[Int, String]] =
      DictEx(TDictItem(1, "11"), TDictItem(2, "12"))
    val expected: DictEx[Int, Int, ADictItem[Int, Int]] =
      DictEx(ADictItem(1, 11), ADictItem(2, 12))
    assertEquals(dict.map(_.toInt), expected)
  }

  test("prepend") {
    val dict: DictEx[Int, String, TDictItem[Int, String]] =
      DictEx(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    val actual: DictEx[Int, String, DictItem[Int, String]] =
      ADictItem(3, "aa") +: dict
    val expected: DictEx[Int, String, DictItem[Int, String]] =
      DictEx(ADictItem(3, "aa"), TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(actual, expected)
  }
}
