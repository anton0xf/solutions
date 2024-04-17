package unit5.lesson1

import munit.FunSuite

class CoprimeSpec extends FunSuite {
  test("sample") {
    assertEquals(Coprime.getCoprimes(4),
      List((1, 1), (1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)))
  }
}
