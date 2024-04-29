package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/4?unit=81046

import munit.FunSuite
import unit6_coll.lesson2.Primes._

class PrimesSpec extends FunSuite {
  test("isPrime") {
    assertEquals((2L to 20).filter(isPrime).toList, List(2L, 3, 5, 7, 11, 13, 17, 19))
    assertEquals(isPrime(101), true)
    assertEquals(isPrime(102), false)
  }

  test("list") {
    assertEquals(list.take(8).toList, List(2L, 3, 5, 7, 11, 13, 17, 19))
  }
}
