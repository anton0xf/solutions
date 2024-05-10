package unit6_coll.lesson2

import munit.FunSuite

class DiffListSpec extends FunSuite {
  test("result") {
    val dl = new DiffListImpl[Int](1 :: _)
    assertEquals(dl.result, List(1))
  }

  test("prepend") {
    val dl = new DiffListImpl[Int](1 :: _)
    val result = dl.prepend(List(2, 3)).result
    assertEquals(result, List(2, 3, 1))
  }

  test("prepend twice") {
    val dl = new DiffListImpl[Int](1 :: _)
    val result = dl.prepend(List(2, 3)).prepend(List(4, 5)).result
    assertEquals(result, List(4, 5, 2, 3, 1))
  }

  test("append and prepend") {
    val l1 = List(1, 2, 3)
    val l2 = List(4, 5, 6)
    val dl = new DiffListImpl[Int](identity)
    val result = dl.append(l2).prepend(l1).result
    assertEquals(result, List(1, 2, 3, 4, 5, 6))
  }
}
