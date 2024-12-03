//> using target.scope test
import Day02.*

class Day02Test extends munit.FunSuite {
  test("diff") {
    assertEquals(diff(List(1, 2, 0, 4)), List(1, -2, 4))
  }
  test("inRange") {
    assertEquals(inRange(0), false)
    assertEquals(inRange(1), true)
    assertEquals(inRange(2), true)
    assertEquals(inRange(3), true)
    assertEquals(inRange(4), false)
  }
  test("isSafe") {
    assertEquals(isSafe(List(7, 6, 4, 2, 1)), true)
    assertEquals(isSafe(List(1, 2, 7, 8, 9)), false)
    assertEquals(isSafe(List(9, 7, 6, 2, 1)), false)
    assertEquals(isSafe(List(1, 3, 2, 4, 5)), false)
    assertEquals(isSafe(List(8, 6, 4, 4, 1)), false)
    assertEquals(isSafe(List(1, 3, 6, 7, 9)), true)
  }
  test("isSafe2") {
    assertEquals(isSafe2(List(7, 6, 4, 2, 1)), true)
    assertEquals(isSafe2(List(1, 2, 7, 8, 9)), false)
    assertEquals(isSafe2(List(9, 7, 6, 2, 1)), false)
    assertEquals(isSafe2(List(1, 3, 2, 4, 5)), true)
    assertEquals(isSafe2(List(8, 6, 4, 4, 1)), true)
    assertEquals(isSafe2(List(1, 3, 6, 7, 9)), true)
  }
}
