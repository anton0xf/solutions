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
    assertEquals(isSafe2(List(75, 77, 72, 70, 69)), true)
  }
  test("isInc2") {
    assertEquals(isInc2(List(2, 5, 7, 8)), true)
    assertEquals(isInc2(List(2, 2, 0, 5, 7, 8)), false)
    assertEquals(isInc2(List(2, 0, 5, 7, 8)), true)
    assertEquals(isInc2(List(2, 0, 5, 0, 7, 8)), false)
    assertEquals(isInc2(List(2, 0, 1, 4)), true)
    assertEquals(isInc2(List(0, 1, 4, 0)), true)
    assertEquals(isInc2(List(0, 1, 4, 0, 1)), false)
  }
  test("isDec2") {
    assertEquals(isDec2(List(75, 77, 72, 70, 69)), true)
  }
}
