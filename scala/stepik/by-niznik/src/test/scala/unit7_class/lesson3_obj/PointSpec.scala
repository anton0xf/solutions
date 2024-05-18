package unit7_class.lesson3_obj

import munit.FunSuite

class PointSpec extends FunSuite {
  import Point._

  test("show") {
    assertEquals(show(Point(1, 2, 3)), "1.0 2.0 3.0")
  }

  test("average of empty list") {
    assertEquals(show(average(List())), "0.0 0.0 0.0")
  }

  test("Sample 1") {
    val ps = List(Point(1, 2.5, 4), Point(4, 3.5, 6))
    assertEquals(show(average(ps)), "2.5 3.0 5.0")
  }

  test("Sample 2") {
    val ps = List(Point(1, 2, 3), Point(4, 5, 6), Point(7, 8, 9))
    assertEquals(show(average(ps)), "4.0 5.0 6.0")
  }
}
