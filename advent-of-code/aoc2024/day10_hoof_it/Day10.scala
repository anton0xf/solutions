import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day10 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day10_hoof_it/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
    }
  }

  case class Pos(i: Int, j: Int) {
    def inside(size: (Int, Int)): Boolean =
      (0 until size._1).contains(i) &&
        (0 until size._2).contains(j)

    def +(p: Pos): Pos = Pos(i + p.i, j + p.j)
  }

  val dirs: Set[Pos] = Set(Pos(0, 1), Pos(1, 0), Pos(0, -1), Pos(-1, 0))

  case class Input(field: Vector[Vector[Int]]) {
    val size: (Int, Int) = (field.size, field(0).size)

    def get(p: Pos): Option[Int] = field.lift(p.i).flatMap(_.lift(p.j))

    def findPos(x: Int): List[Pos] = (for {
      i <- 0 until size._1
      j <- 0 until size._2
      if x == field(i)(j)
    } yield Pos(i, j)).toList

    def next(p: Pos): Set[Pos] = {
      val x = get(p).get
      dirs.map(p + _).filter { q => get(q).map(_ == x + 1).getOrElse(false) }
    }

    def trailEnds(cur: Set[Pos]): Set[Pos] =
      if get(cur.head).get == 9 then cur
      else trailEnds(cur.flatMap(next))

  }

  def parseInput(lines: Iterator[String]): Input = Input(
    lines.map(_.map(parseDigit).toVector).toVector
  )
  def parseDigit(ch: Char): Int = {
    val d = ch - '0'
    if (0 to 9).contains(d) then d else -1
  }

  // part 1
  def solution1(input: Input): Int = {
    input.findPos(0).map(p => input.trailEnds(Set(p))).map(_.size).sum
  }

  // part 2
}
