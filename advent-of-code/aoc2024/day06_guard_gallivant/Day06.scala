import scala.annotation.{tailrec, targetName}
import scala.util.Using
import scala.io.Source

object Day06 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day06_guard_gallivant/input")) { source =>
      val input: Input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
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
    val nextPos: Pos = pos + dir

    val inside: Boolean = (0 until size._1).contains(pos.i) &&
      (0 until size._2).contains(pos.j)

    @tailrec
    final def next: State = {
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

  // part 2
  case class FullPos(pos: Pos, dir: Pos)

  def solution2(input: Input): Int = {
    @tailrec
    def go(st: State, visited: Set[Pos], visitedFull: Set[FullPos], stuckers: Set[Pos]): Int = {
      if !st.inside then stuckers.size
      else {
        val next = st.next
        go(
          st = next,
          visited = visited + st.pos,
          visitedFull = visitedFull + FullPos(st.pos, st.dir),
          stuckers =
            if !visited.contains(next.pos) &&
              hasLoop(st.copy(obstructions = st.obstructions + next.pos), visitedFull)
            then stuckers + next.pos
            else stuckers
        )
      }
    }
    @tailrec
    def hasLoop(st: State, visited: Set[FullPos]): Boolean = st.inside && {
      val pos = FullPos(st.pos, st.dir)
      visited.contains(pos) || hasLoop(st.next, visited + pos)
    }
    go(input.toState, Set(), Set(), Set())
  }

}
