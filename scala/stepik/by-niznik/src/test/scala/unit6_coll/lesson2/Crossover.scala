package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/8?unit=81046

import scala.annotation.tailrec
import scala.io.StdIn

object Crossover {
  def main(args: Array[String]): Unit = {
    val points: List[Int] = StdIn.readLine().split("\\s+").map(_.toInt).toList
    val chr1: List[Char] = StdIn.readLine().toList
    val chr2: List[Char] = StdIn.readLine().toList
    // put your code here
    val (r1, r2) = cross(points, chr1, chr2)
    println(r1.mkString)
    println(r2.mkString)
  }

  def cross[T](points: List[Int], chr1: List[T], chr2: List[T]): (List[T], List[T]) = {
    case class St(swap: Boolean, points: List[Int], acc: List[(T, T)])
    def swapIf(pair: (T, T), swap: Boolean): (T, T) = if (swap) pair.swap else pair
    def go(st: St, x: ((T, T), Int)): St = {
      val (pair, id) = x
      if (st.points.isEmpty || id < st.points.head) {
        St(st.swap, st.points, swapIf(pair, st.swap) :: st.acc)
      } else {
        assert(id == st.points.head)
        St(!st.swap, st.points.tail, swapIf(pair, !st.swap) :: st.acc)
      }
    }
    (chr1 zip chr2).zipWithIndex.foldLeft(St(swap = false, points, Nil))(go).acc.reverse.unzip
  }
}
