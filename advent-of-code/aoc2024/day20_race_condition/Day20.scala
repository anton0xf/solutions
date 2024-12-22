import scala.annotation.{tailrec, targetName}
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day20 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day20_race_condition/input")) { source =>
      val input = parseInput(source.getLines().toList)
      println(s"part 1: ${solution1(input, 100)}")
      println(s"part 2: ${solution2(input, 20, 100)}")
    }
  }

  case class Track(start: Vec, end: Vec, path: Set[Vec], size: (Int, Int)) {
    def in(p: Vec): Boolean = (0 until size._1).contains(p.x) &&
      (0 until size._2).contains(p.y)
    def wall(p: Vec): Boolean = in(p) && p != start && p != end && !path.contains(p)
    def onPath(p: Vec): Boolean = in(p) && (p == start || p == end || path.contains(p))
  }

  case class Vec(x: Int, y: Int) {
    @targetName("plus")
    def +(p: Vec): Vec = Vec(x + p.x, y + p.y)
    def neighbours: Set[Vec] = dirs.map(+)

    /** circle in Manhattan geometry
      *
      * <code> |x - px| + |y - py| = r </code>
      */
    def circle(r: Int): Seq[Vec] = (-r to r).flatMap { d =>
      val px = x + d
      val r1 = r - d.abs
      if r1 == 0 then Seq(Vec(px, y))
      else Seq(y - r1, y + r1).map(Vec(px, _))
    }
  }

  val dirs: Set[Vec] = Set(Vec(1, 0), Vec(0, 1), Vec(-1, 0), Vec(0, -1))

  def parseInput(lines: List[String]): Track = {
    val path = for {
      (line, y) <- lines.zipWithIndex
      (ch, x) <- line.zipWithIndex
      if ch != '#'
    } yield Vec(x, y) -> ch
    Track(
      start = path.find(_._2 == 'S').map(_._1).get,
      end = path.find(_._2 == 'E').map(_._1).get,
      path = path.filter(_._2 == '.').map(_._1).toSet,
      size = (lines.head.length, lines.size)
    )
  }

  // part 1
  def solution1(track: Track, threshold: Int): Int = {
    val path = followPath(track)
    val nums = path.iterator.zipWithIndex.toMap
    // println(path)
    def cheats(p: Vec): Int = {
      val num = nums(p)
      val walls = p.neighbours.filter(track.wall)
      val ends = walls.flatMap(_.neighbours).filter { q =>
        nums.get(q).exists(_ >= num + 2 + threshold)
      }
      // if ends.nonEmpty then println(s"cheats: $p -> $ends")
      ends.size
    }
    path.map(cheats).sum
  }

  def followPath(track: Track): Vector[Vec] = {
    @tailrec
    def go(p: Vec, acc: Vector[Vec]): Vector[Vec] = {
      val acc1 = acc :+ p
      if p == track.end then acc1
      else {
        val p1 = p.neighbours.find(q => track.onPath(q) && !acc.lastOption.contains(q)).get
        go(p1, acc1)
      }
    }
    go(track.start, Vector())
  }

  // part 2
  def solution2(track: Track, maxR: Int, threshold: Int): Int = {
    val path = followPath(track)
    val nums = path.iterator.zipWithIndex.toMap

    // println(path)
    def cheats(p: Vec): Int = {
      val num = nums(p)
      (2 to maxR).map { r =>
        val ends = p.circle(r).filter(q => nums.get(q).exists(_ >= num + r + threshold))
        // if ends.nonEmpty then println(s"cheats: $p -> $ends")
        ends.size
      }.sum
    }

    path.map(cheats).sum
  }
}
