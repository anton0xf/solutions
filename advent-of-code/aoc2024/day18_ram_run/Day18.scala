import scala.annotation.{tailrec, targetName}
import scala.collection.immutable
import scala.collection.immutable.Queue
import scala.util.Using
import scala.io.Source

object Day18 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day18_ram_run/input")) { source =>
      val input = parseInput(source.getLines())
      val corner = Vec(70, 70)
      val mem1 = Mem(corner, input.take(1024).toSet)
      println(s"part 1: ${solution1(mem1)}")
    }
  }

  type Input = List[Vec]

  case class Vec(x: Int, y: Int) {
    @targetName("plus")
    def +(p: Vec): Vec = Vec(x + p.x, y + p.y)
    def neighbours: Set[Vec] = dirs.map(this + _)
  }

  val dirs: Set[Vec] = Set(Vec(0, 1), Vec(1, 0), Vec(0, -1), Vec(-1, 0))

  case class Mem(corner: Vec, bytes: Set[Vec]) {
    def show: String = (0 to corner.y)
      .map { y =>
        (0 to corner.x).map { x =>
          if bytes.contains(Vec(x, y)) then '#' else '.'
        }.mkString
      }
      .mkString("\n")

    def in(p: Vec): Boolean = (0 to corner.x).contains(p.x) && (0 to corner.y).contains(p.y)
    def neighbours(p: Vec): Set[Vec] = p.neighbours.filter { p => in(p) && !bytes.contains(p) }
  }

  def parseInput(lines: IterableOnce[String]): Input = lines.iterator.map { line =>
    line.split(',').map(_.toInt) match
      case Array(x, y) => Vec(x, y)
      case _           => throw new Exception(s"unexpected format: $line")
  }.toList

  // part 1
  def solution1(mem: Mem): Int = {
    val p = findPath(mem)
    p.get.size - 1
  }

  def findPath(mem: Mem): Option[List[Vec]] = {
    val start = Vec(0, 0)
    val end = mem.corner
    @tailrec
    def bfs(q: Queue[Vec], visited: Set[Vec], prev: Map[Vec, Vec]): Option[List[Vec]] = {
      if q.isEmpty then None
      else {
        val (p, q1) = q.dequeue
        if p == end then Some(backtrack(p, prev))
        else if visited.contains(p) then bfs(q1, visited, prev)
        else {
          val ns = mem.neighbours(p)
          bfs(
            q1.enqueueAll(ns),
            visited + p,
            ns.foldLeft(prev) { (prev, n) => prev.updatedWith(n)(_.orElse(Some(p))) }
          )
        }
      }
    }
    def backtrack(p: Vec, prev: Map[Vec, Vec]): List[Vec] = {
      @tailrec
      def go(acc: List[Vec]): List[Vec] = {
        val p = acc.head
        if p == start then acc else go(prev(p) :: acc)
      }
      go(p :: Nil)
    }
    bfs(Queue(start), Set(), Map())
  }

  // part 2
}
