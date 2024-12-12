import scala.annotation.tailrec
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day12 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day12_garden_groups/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  case class Input(map: Vector[Vector[Char]]) {
    def apply(p: Pos): Option[Char] = map.lift(p.i).flatMap(_.lift(p.j))

    def positions: Set[Pos] = map.indices.flatMap(i => map.head.indices.map(j => Pos(i, j))).toSet
  }

  case class Pos(i: Int, j: Int) {
    def +(p: Pos): Pos = Pos(i + p.i, j + p.j)
    def neighbours: Set[Pos] = dirs.map(this + _)
    def rotRight: Pos = Pos(j, -i)
    def rotLeft: Pos = Pos(-j, i)
  }

  val dirs: Set[Pos] = Set(Pos(0, 1), Pos(1, 0), Pos(0, -1), Pos(-1, 0))

  def parseInput(lines: Iterator[String]): Input = Input(lines.map(_.toVector).toVector)

  // part 1
  def solution1(input: Input): BigInt = {
    regions(input).map { region => BigInt(region.size) * regionPerimeter(region) }.sum
  }

  def regions(input: Input): List[Set[Pos]] = {
    @tailrec
    def go(q: Set[Pos], regions: List[Set[Pos]]): List[Set[Pos]] = {
      if q.isEmpty then regions
      else {
        val region = searchRegion(q.head, input)
        assert(region.forall(q.contains))
        go(q -- region, region :: regions)
      }
    }
    go(input.positions, Nil)
  }

  def searchRegion(p: Pos, input: Input): Set[Pos] = {
    @tailrec
    def go(q: List[Pos], region: Set[Pos]): Set[Pos] = {
      q match {
        case Nil => region
        case p :: q =>
          if region.contains(p) then go(q, region)
          else {
            val ch = input(p).get
            val ns = p.neighbours.filter(n => input(n).contains(ch)) -- region
            go(q :++ ns, region + p)
          }
      }
    }
    go(List(p), Set())
  }

  def regionPerimeter(region: Set[Pos]) = {
    region.iterator.map { p => p.neighbours.count(!region.contains(_)) }.sum
  }

  // part 2
  def solution2(input: Input): BigInt = {
    regions(input).map { region => BigInt(region.size) * regionSides(region) }.sum
  }

  def regionSides(region: Set[Pos]): Int = {
    val sides = (for {
      p <- region.iterator
      dir <- dirs
      if !region.contains(p + dir)
    } yield (p, dir)).toSet

    /** go around one of the region's boundaries, counting corners */
    @tailrec
    def go(p: Pos, dir: Pos, visited: Set[(Pos, Pos)], corners: Int): (Set[(Pos, Pos)], Int) = {
      if visited.contains((p, dir)) then (visited, corners)
      else {
        val nextVisited = visited + ((p, dir))
        val rDir = dir.rotRight
        val n = p + rDir
        if region.contains(n) then {
          val n2 = n + dir
          if region.contains(n2)
          then go(n2, dir.rotLeft, nextVisited, corners + 1)
          else go(n, dir, nextVisited, corners)
        } else go(p, rDir, nextVisited, corners + 1)
      }
    }

    /** iterate over all boundaries */
    @tailrec
    def iter(sides: Set[(Pos, Pos)], acc: Int): Int = {
      val (p, dir) = sides.head
      val (visited, corners) = go(p, dir, Set(), 0)
      val newSides = sides -- visited
      val newAcc = acc + corners
      if newSides.isEmpty then newAcc else iter(newSides, newAcc)
    }

    iter(sides, 0)
  }

}
