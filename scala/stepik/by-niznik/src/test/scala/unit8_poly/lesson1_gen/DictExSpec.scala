package unit8_poly.lesson1_gen

import munit.FunSuite

class DictExSpec extends FunSuite {
  test("head A") {
    val dict: DictEx[Int, String, ADictItem] = DictEx.make(ADictItem(1, "asdf"), ADictItem(2, "qq"))
    assertEquals(dict.head, ADictItem(1, "asdf"))
  }

  test("head T") {
    val dict: DictEx[Int, String, TDictItem] = DictEx.make(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(dict.head, TDictItem(1, "asdf"))
  }

  test("head AT") {
    val dict: DictEx[Int, String, DictItem] = DictEx.make(ADictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(dict.head, ADictItem(1, "asdf"))
  }

  test("map") {
    val dict: DictEx[Int, String, TDictItem] = DictEx.make(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    val expected: DictEx[Int, String, ADictItem] = DictEx.make(ADictItem(1, "asdf_"), ADictItem(2, "qq_"))
    assertEquals(dict.map(_ + "_"), expected)
  }

  test("map to other type") {
    val dict: DictEx[Int, String, TDictItem] = DictEx.make(TDictItem(1, "11"), TDictItem(2, "12"))
    val expected: DictEx[Int, Int, ADictItem] = DictEx.make(ADictItem(1, 11), ADictItem(2, 12))
    assertEquals(dict.map(_.toInt), expected)
  }

  test("prepend") {
    val dict: DictEx[Int, String, TDictItem] = DictEx.make(TDictItem(1, "asdf"), TDictItem(2, "qq"))
    val actual: DictEx[Int, String, DictItem] = ADictItem(3, "aa") +: dict
    val expected: DictEx[Int, String, DictItem] =
      DictEx.make(ADictItem(3, "aa"), TDictItem(1, "asdf"), TDictItem(2, "qq"))
    assertEquals(actual, expected)
  }

  test("prepend other type") {
    class A(val n: Int) {
      override def equals(obj: Any): Boolean =
        obj.isInstanceOf[A] && obj.asInstanceOf[A].n == n
    }
    object A { def apply(n: Int) = new A(n) }
    class B(n: Int, val s: String) extends A(n) {
      override def equals(obj: Any): Boolean =
        super.equals(obj) && obj.isInstanceOf[B] && obj.asInstanceOf[B].s == s
    }
    object B { def apply(n: Int, s: String) = new B(n, s) }

    val dict: DictEx[Int, B, DictItem] = DictEx.make(ADictItem(1, B(10, "a")), TDictItem(2, B(20, "qq")))
    val actual: DictEx[Int, A, DictItem] = ADictItem(3, A(30)) +: dict
    val expected: DictEx[Int, A, DictItem] =
      DictEx.make(ADictItem(3, A(30)), ADictItem(1, B(10, "a")), TDictItem(2, B(20, "qq")))
    assertEquals(actual, expected)
  }
}
