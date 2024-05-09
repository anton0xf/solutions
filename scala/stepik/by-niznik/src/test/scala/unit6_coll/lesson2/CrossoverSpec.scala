package unit6_coll.lesson2

import munit.FunSuite

class CrossoverSpec extends FunSuite {
  test("cross") {
    assertEquals(
      Crossover.cross(
        List(1, 3),
        List('x', 'x', 'x', 'x', 'x'),
        List('y', 'y', 'y', 'y', 'y')
      ),
      (
        List('x', 'y', 'y', 'x', 'x'),
        List('y', 'x', 'x', 'y', 'y')
      )
    )

    assertEquals(
      Crossover.cross(List(2, 4, 5), "aaaaaaa".toList, "ddddddd".toList),
      ("aaddadd".toList, "ddaadaa".toList)
    )
    assertEquals(
      Crossover.cross(List(2, 4, 5, 10), "aaaaaaa".toList, "ddddddd".toList),
      ("aaddadd".toList, "ddaadaa".toList)
    )
  }
}
