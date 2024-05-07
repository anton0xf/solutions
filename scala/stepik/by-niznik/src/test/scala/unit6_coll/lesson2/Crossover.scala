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

  def cross(
      points: List[Int],
      chr1: List[Char],
      chr2: List[Char]
  ): (List[Char], List[Char]) = {
    @tailrec
    def go(
        points: List[Int],
        pairs: Iterable[(Char, Char)],
        id: Int,
        swap: Boolean,
        acc: List[(Char, Char)]
    ): List[(Char, Char)] = {
      if (points.isEmpty) {
        if (swap) acc.reverse ++ pairs.map(_.swap).toList
        else acc.reverse ++ pairs.toList
      } else if (pairs.isEmpty) {
        acc.reverse
      } else if (id < points.head) {
        val pair = pairs.head
        val newPair = if (swap) pair.swap else pair
        go(points, pairs.tail, id + 1, swap, newPair :: acc)
      } else {
        assert(id == points.head)
        val newSwap = !swap
        val pair = pairs.head
        val newPair = if (newSwap) pair.swap else pair
        go(points.tail, pairs.tail, id + 1, newSwap, newPair :: acc)
      }
    }
    val pairs = chr1 lazyZip chr2
    go(points, pairs, id = 0, swap = false, acc = Nil).unzip
  }
}
