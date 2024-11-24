package part4

import scala.collection.immutable.WrappedString

object Step_4_2_10 {
  def main(args: Array[String]): Unit = {
    val phone = "9-876-543-21-09"
    printMap(countNumbers(phone))
    printMap(countNumbers0(phone))
  }

  private def printMap(m: Map[Char, Int]): Unit = {
    val kvs: List[Int] = for { k <- List.range(0, 10) } yield m(('0' + k).toChar)
    println(kvs.mkString(""))
  }

  private def countNumbers(s: String): Map[Char, Int] =
    (s.groupBy(identity) - '-').mapValues(_.length)

  private def countNumbers0(s: String): Map[Char, Int] =
    s.foldLeft(Map[Char, Int]().withDefaultValue(0)) { case (acc, letter) =>
      if (letter != '-') acc + (letter -> (1 + acc(letter)))
      else acc
    }
}
