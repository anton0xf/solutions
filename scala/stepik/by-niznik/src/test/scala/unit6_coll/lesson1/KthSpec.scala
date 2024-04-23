package unit6_coll.lesson1

import munit.FunSuite
import scala.util.Random

class KthSpec extends FunSuite {
  test("samples") {
    assertEquals(Kth.kOrder(List(3), 1), 3)
    assertEquals(Kth.kOrder(List(1, 2, 3), 1), 1)
    assertEquals(Kth.kOrder(List(1, 2, 3, 4, 5, 6, 7), 7), 7)
    assertEquals(Kth.kOrder(List(3, 8, 1, 12, 23), 4), 12)
    assertEquals(Kth.kOrder(List(4, 7, 6, 5, 12, 9, 5), 3), 5)
  }

  test("compare with nth of sorted on random lists") {
    def ref(xs: List[Int], k: Int): Int = xs.sorted.apply(k - 1)
    val rnd = new Random(0)
    for (i <- 1 to 100) {
      val xs: List[Int] = List.fill(rnd.nextInt(100) + 2)(rnd.nextInt(300))
      val k: Int = rnd.nextInt(xs.length - 1) + 1
      val actual = Kth.kOrder(xs, k)
      val expected = ref(xs, k)
      assertEquals(actual, expected, s"wrong $k-th of $xs")
    }
  }
}
