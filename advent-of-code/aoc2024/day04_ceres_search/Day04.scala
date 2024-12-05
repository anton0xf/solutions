import scala.util.Using
import scala.io.Source
import scala.util.matching.Regex

object Day04 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day04_ceres_search/input")) { source =>
      val input = source.getLines().map(_.toVector).toVector
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  type Input = Vector[Vector[Char]]

  def get(input: Input, pos: (Int, Int)): Option[Char] = input.lift(pos._1).flatMap(_.lift(pos._2))
  def getAll(input: Input, poss: (Int, Int)*): Seq[Char] = poss.flatMap(get(input, _))

  // part 1
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
      get(input, (i,j)).exists { nextCh =>
        if word.head == nextCh then go((i, j), word.tail) else false
      }
    }
    go(pos, word.tail)
  }

  // part 2
  def solution2(input: Input): Int = {
    val found = for {
      (line, i) <- input.zipWithIndex
      (ch, j) <- line.zipWithIndex
      if ch == 'A'
    } yield checkPattern(input, (i, j))
    found.count(identity)
  }

  def checkPattern(input: Input, pos: (Int, Int)): Boolean = {
    def check(diag: Seq[Char]): Boolean = diag.toSet == Set('M', 'S')
    val diag1 = getAll(input, (pos._1 - 1, pos._2 - 1), (pos._1 + 1, pos._2 + 1))
    val diag2 = getAll(input, (pos._1 - 1, pos._2 + 1), (pos._1 + 1, pos._2 - 1))
    check(diag1) && check(diag2)
  }
}
