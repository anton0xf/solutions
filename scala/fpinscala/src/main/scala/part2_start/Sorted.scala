package part2_start

import scala.annotation.tailrec

/*
exercise 2.2.
Implement isSorted, which checks whether an Array[A] is sorted
according to a given comparison function
 */
object Sorted {
  @tailrec
  def isSorted[A](as: Array[A], ordered: (A, A) => Boolean): Boolean = {
    as.length < 2 || (ordered(as(0), as(1)) && isSorted(as.tail, ordered))
  }

  def isSorted2[A](as: Array[A], ordered: (A, A) => Boolean): Boolean = {
    @tailrec
    def go(i: Int): Boolean = (i + 1 >= as.length) ||
      (ordered(as(i), as(i + 1)) && go(i + 1))
    go(0)
  }

}
