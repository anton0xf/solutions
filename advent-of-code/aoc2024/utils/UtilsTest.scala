//> using target.scope test
class UtilsTest extends munit.FunSuite {
  test("splitBy") {
    val p: Int => Boolean = _ == 0
    assertEquals(List(1, 0, 2, 1, 0).splitBy(p), LazyList(List(1), List(2, 1)))
    assertEquals(List(0, 1, 0, 0, 2).splitBy(p), LazyList(List(1), List(2)))
    assertEquals(List().splitBy(_ == 0), LazyList.empty)
    assertEquals(List(0, 0, 0).splitBy(p), LazyList.empty)
    assertEquals(List(0, 1).splitBy(p), LazyList(List(1)))
    assertEquals(List(1, 0).splitBy(p), LazyList(List(1)))
    assertEquals(List(1).splitBy(p), LazyList(List(1)))

    val count = 100_000
    assertEquals((0 to (count * 2)).splitBy(_ % 2 == 1), (0 to count).map(n => List(n*2)))
  }
}
