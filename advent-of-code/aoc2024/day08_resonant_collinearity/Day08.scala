import scala.util.Using
import scala.io.Source

object Day08 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day08_resonant_collinearity/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
    }
  }

  case class Input(size: (Int, Int), map: Map[Pos, Char])
  case class Pos(i: Int, j: Int) {
    def +(p: Pos): Pos = Pos(i + p.i, j + p.j)
    def -(p: Pos): Pos = Pos(i - p.i, j - p.j)

    def inside(size: (Int, Int)): Boolean =
      (0 until size._1).contains(i) &&
        (0 until size._2).contains(j)
  }

  def parseInput(lines: Iterator[String]): Input = {
    val res = lines.zipWithIndex.map { (line, i) =>
      val ps = line.zipWithIndex
        .withFilter { (ch, j) => ch != '.' }
        .map { (ch, j) => Pos(i, j) -> ch }
      line.length -> ps
    }.toList
    val len = res.map(_._1).head
    val ps = res.flatMap(_._2).toMap
    Input((res.size, len), ps)
  }

  // part 1
  def solution1(input: Input): Int = {
    val as = for {
      (ch, ps) <- input.map.groupMap(_._2)(_._1)
      p1 <- ps
      p2 <- ps
      if p1 != p2
      antinode <- antinodes(p1, p2)
      if antinode.inside(input.size)
    } yield antinode
    as.toSet.size
  }

  def antinodes(p1: Pos, p2: Pos): List[Pos] = List(p2 + p2 - p1, p1 + p1 - p2)
}
