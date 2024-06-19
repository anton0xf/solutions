package unit8_poly.lesson4_implicit

import munit.FunSuite
import Ratio.RatioOps
import Ratio.ordering

import scala.math.Ordering.Implicits._

class RatioSpec extends FunSuite {
  test("ratio creation") {
    val r1 = Ratio(2, 3)
    assertEquals(r1.num, BigInt(2))
    assertEquals(r1.den, BigInt(3))
  }

  test("ratio creation with simplification") {
    val r1 = Ratio(20, 30)
    assertEquals(r1.num, BigInt(2))
    assertEquals(r1.den, BigInt(3))
    assertEquals(r1, Ratio(6, 9))
  }

  test("ratio creation with negative denominator") {
    val r1 = Ratio(-6, -9)
    assertEquals(r1.num, BigInt(2))
    assertEquals(r1.den, BigInt(3))
    assertEquals(r1, Ratio(10, 15))
  }

  test("ratio creation with syntax sugar") {
    val r1 = 30 \\ 60
    assertEquals(r1.num, BigInt(1))
    assertEquals(r1.den, BigInt(2))
  }

  test("ratio ordering") {
    assertEquals(1 \\ 2 < 2 \\ 3, true)
    assertEquals(1 \\ 2 > 2 \\ 3, false)
    assertEquals(4 \\ 8 < 2 \\ 3, true)

    val rs = List(4 \\ 8, 5 \\ 15, 6 \\ 9)
    assertEquals(rs.sorted, List(1 \\ 3, 1 \\ 2, 2 \\ 3))
    assertEquals(rs.min, 1 \\ 3)
  }
}
