package part4

import scala.annotation.tailrec

object Step_4_8_3 {
  def duplicate[T](xs: List[T], n: Int): List[T] = {
    @tailrec
    def go(xs: List[T], acc: List[T]): List[T] = xs match {
      case Nil => acc
      case x :: xs => go(xs, List.fill(n)(x) ++ acc)
    }
    go(xs.reverse, Nil)
  }

  def main(args: Array[String]): Unit = {
    println(duplicate(List('a', 'b'), 2))
  }
}