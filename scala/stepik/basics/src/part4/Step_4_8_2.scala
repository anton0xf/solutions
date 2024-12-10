package part4

import scala.annotation.tailrec

object Step_4_8_2 {
  def parseVersion(v: String): List[Int] = v.split('.').map(_.toInt).toList

  def compare(v1: String, v2: String): Int = {
    @tailrec
    def go(v1: List[Int], v2: List[Int]): Int = (v1, v2) match {
      case (Nil, Nil) => 0
      case (Nil, _)   => go(List(0), v2)
      case (_, Nil)   => go(v1, List(0))
      case (x1 :: v1, x2 :: v2) =>
        if (x1 < x2) -1
        else if (x1 > x2) 1
        else go(v1, v2)
    }
    go(parseVersion(v1), parseVersion(v2))
  }
}
