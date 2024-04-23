package unit6_coll.lesson1
// https://stepik.org/lesson/106540/step/7?unit=81066

import scala.annotation.tailrec
import scala.io.StdIn

object Kth {
  def main(args: Array[String]): Unit = {
    val k = StdIn.readInt()
    val xs = StdIn.readLine().split(' ').map(_.toInt).toList
    println(kOrder(xs, k))
  }

  @tailrec
  def kOrder(xs: List[Int], k: Int): Int = {
    val x = xs.head
    val (le, gt) = xs.tail.partition(_ <= x)
    if (le.length + 1 == k) x
    else if (le.length >= k) kOrder(le, k)
    else kOrder(gt, k - le.length - 1)
  }
}
