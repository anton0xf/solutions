import scala.util.Using
import scala.io.Source
import scala.util.matching.Regex

object Day04 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day04_ceres_search/input")) { source =>
      val input = source.getLines().map(_.toVector).toVector
      // part 1
      val res1 = solution1(input)
      println(s"part 1: $res1")
    }
  }

  type Input = Vector[Vector[Char]]

  val word = "XMAS".toList
  val dirs1 = List(-1, 0, 1)
  val dirs = for {
    i <- dirs1
    j <- dirs1
    if !(i == 0 && j == 0)
  } yield (i, j)

  def solution1(input: Input): Int = {
    val foundWords = for {
      (line, i) <- input.zipWithIndex
      (ch, j) <- line.zipWithIndex
      if ch == word.head
      dir <- dirs
    } yield findWord(input, (i, j), dir)
    foundWords.count(identity)
  }

  def findWord(input: Input, pos: (Int, Int), dir: (Int, Int)): Boolean = {
    def go(pos: (Int, Int), word: List[Char]): Boolean = word.isEmpty || {
      val i = pos._1 + dir._1
      val j = pos._2 + dir._2
      input.lift(i).flatMap(_.lift(j)).exists { nextCh =>
        if word.head == nextCh then go((i, j), word.tail) else false
      }
    }
    go(pos, word.tail)
  }
}
