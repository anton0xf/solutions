package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/4?unit=81046

import munit.FunSuite
import unit6_coll.lesson2.Primes._

class PrimesSpec extends FunSuite {
  test("isPrime") {
    assertEquals((1 to 20).filter(isPrime).toList, List(1, 2, 3, 5, 7, 11, 13, 17, 19))
  }
}
