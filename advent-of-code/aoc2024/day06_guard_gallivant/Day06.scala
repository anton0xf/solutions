import scala.annotation.{tailrec, targetName}
import scala.util.Using
import scala.io.Source

object Day06 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day06_guard_gallivant/input")) { source =>
      val input: Input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
    }
  }

  case class Pos(i: Int, j: Int) {
    def +(p: Pos): Pos = Pos(i + p.i, j + p.j)
    def rotRight: Pos = Pos(j, -i)
  }

  case class Input(size: (Int, Int), start: Pos, obstructions: Set[Pos]) {
    def toState: State = State(
      size = size,
      obstructions = obstructions,
      pos = start,
      dir = Pos(-1, 0)
    )
  }

  def parseInput(lines: Iterator[String]): Input = {
    case class ParsedLine(i: Int, len: Int, start: Option[Int], obstructions: Seq[Int])
    val ls = lines
      .filter(_.nonEmpty)
      .zipWithIndex
      .map { (line, i) =>
        ParsedLine(
          i = i,
          len = line.length,
          start = findCharIndexes(line, '^').headOption,
          obstructions = findCharIndexes(line, '#')
        )
      }
      .toList
    Input(
      size = (ls.size, ls.head.len),
      start = ls.flatMap { line => line.start.map(Pos(line.i, _)) }.head,
      obstructions = ls.flatMap { line => line.obstructions.map(Pos(line.i, _)) }.toSet
    )
  }

  def findCharIndexes(line: String, ch: Char): Seq[Int] =
    line.zipWithIndex.filter(_._1 == ch).map(_._2)

  case class State(size: (Int, Int), obstructions: Set[Pos], pos: Pos, dir: Pos) {
    def inside: Boolean = (0 until size._1).contains(pos.i) &&
      (0 until size._2).contains(pos.j)

    @tailrec
    final def next: State = {
      val nextPos = pos + dir
      if obstructions.contains(nextPos)
      then copy(dir = dir.rotRight).next
      else copy(pos = nextPos)
    }
  }

  // part 1
  def solution1(input: Input): Int = {
    def go(st: State, visited: Set[Pos]): Int = {
      if st.inside then go(st.next, visited + st.pos)
      else visited.size
    }
    go(input.toState, Set())
  }

}
