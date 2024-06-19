package part2_start

import munit.FunSuite

class SortedTest extends FunSuite {
  def check(
      isSorted: (Array[Int], (Int, Int) => Boolean) => Boolean
  )(as: Array[Int]): Boolean = isSorted(as, _ <= _)

  for (
    (name, f) <- List(
      "isSorted" -> Sorted.isSorted[Int] _,
      "isSorted2" -> Sorted.isSorted2[Int] _
    )
  ) test(name) {
    assertEquals(check(f)(Array()), true)
    assertEquals(check(f)(Array(1)), true)
    assertEquals(check(f)(Array(1, 1)), true)
    assertEquals(check(f)(Array(1, 2)), true)
    assertEquals(check(f)(Array(2, 1)), false)
    assertEquals(check(f)(Array(1, 2, 2)), true)
    assertEquals(check(f)(Array(1, 2, 3)), true)
    assertEquals(check(f)(Array(1, 3, 2)), false)
    assertEquals(check(f)(Array(2, 1, 3)), false)
  }
}
