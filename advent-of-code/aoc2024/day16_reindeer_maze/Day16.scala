import scala.annotation.{tailrec, targetName}
import scala.collection.immutable.Queue
import scala.collection.{immutable, mutable}
import scala.util.Using
import scala.io.Source
import scala.math.Ordering.OptionOrdering

object Day16 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day16_reindeer_maze/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  case class Input(maze: Set[Vec], start: Vec, end: Vec)

  case class Vec(x: Int, y: Int) {
    override def toString: String = s"[$x,$y]"

    @targetName("plus")
    def +(p: Vec): Vec = Vec(x + p.x, y + p.y)

    /** rotate clockwise */
    def rot: Vec = Vec(-y, x)

    /** rotate counterclockwise */
    def rotBack: Vec = Vec(y, -x)
  }

  case class Pos(p: Vec, dir: Vec) {
    override def toString: String = s"$p${dirsInv(dir)}"
  }

  val dirs: Map[Char, Vec] =
    Map('>' -> Vec(1, 0), '<' -> Vec(-1, 0), '^' -> Vec(0, -1), 'v' -> Vec(0, 1))
  val dirsInv: Map[Vec, Char] = dirs.map(_.swap)
  val initDir: Vec = dirs('>')

  def parseInput(lines: IterableOnce[String]): Input = {
    val ps = for {
      (line, y) <- lines.iterator.zipWithIndex
      (ch, x) <- line.zipWithIndex
      if ch != '.'
    } yield Vec(x, y) -> ch
    val (maze, start, end) = ps.foldLeft((Set[Vec](), None: Option[Vec], None: Option[Vec])) {
      case ((maze, start, end), (p, ch)) =>
        ch match
          case '#' => (maze + p, start, end)
          case 'S' => (maze, start.orElse(Some(p)), end)
          case 'E' => (maze, start, end.orElse(Some(p)))
    }
    Input(maze, start.get, end.get)
  }

  def showMaze(input: Input, path: List[Pos]): String = {
    val ps = path.map(pos => pos.p -> pos.dir).toMap
    (0 to input.maze.map(_.y).max)
      .map { y =>
        (0 to input.maze.map(_.x).max).map { x =>
          val p = Vec(x, y)
          if input.maze.contains(p) then '#'
          else if input.start == p then 'S'
          else if input.end == p then 'E'
          else ps.get(p).map(dirsInv(_)).getOrElse('.')
        }.mkString
      }
      .mkString("\n")
  }

  // part 1
  def solution1(input: Input): Int = {
    val (dist: Int, path: List[Pos]) = dijkstra(input).get
    println(showMaze(input, path)) // TODO remove
    dist
  }

  val moveCost = 1
  val rotCost = 1000
  enum Dist extends Ordered[Dist] {
    override def compare(that: Dist): Int = (this, that) match
      case (Inf, Inf)         => 0
      case (Inf, _)           => 1
      case (_, Inf)           => -1
      case (Val(d1), Val(d2)) => d1 compare d2

    case Inf extends Dist
    case Val(d: Int) extends Dist
  }

  def dijkstra(input: Input): Option[(Int, List[Pos])] = {
    import input.*
    val startPos = Pos(start, initDir)
    val dist = mutable.Map[Pos, Int](startPos -> 0)
    val prev = mutable.Map[Pos, Pos]()
    def posDist(p: Pos): Dist = dist.get(p).map(Dist.Val.apply).getOrElse(Dist.Inf)
    val q = mutable.PriorityQueue[Pos](startPos)(using Ordering.by[Pos, Dist](posDist).reverse)
    val visited = mutable.Set[Pos]()
    @tailrec
    def go(): Option[(Int, List[Pos])] = {
      if q.isEmpty then None
      else {
        val cur = q.dequeue()
        if visited.contains(cur) then go()
        else {
          visited += cur
          val curD = dist(cur)
          if cur.p == end then Some(curD, traceBack(cur, List(cur)))
          else {
            val ns = neighbours(cur)
              .filterNot { case (n @ Pos(p, _), _) => maze.contains(p) || visited.contains(n) }
            ns.foreach { (n, d) =>
              val newD = curD + d
              val oldD = dist.get(n)
              if oldD.isEmpty || oldD.get > newD then {
                dist.put(n, newD)
                prev.put(n, cur)
              }
            }
            q ++= ns.keys
            go()
          }
        }
      }
    }
    @tailrec
    def traceBack(cur: Pos, acc: List[Pos]): List[Pos] =
      if cur == startPos then acc
      else {
        val pos = prev(cur)
        if pos.p == cur.p then traceBack(pos, acc)
        else traceBack(pos, pos :: acc)
      }
    go()
  }

  def neighbours(pos: Pos): Map[Pos, Int] = Map(
    pos.copy(p = pos.p + pos.dir) -> moveCost,
    pos.copy(dir = pos.dir.rot) -> rotCost,
    pos.copy(dir = pos.dir.rotBack) -> rotCost
  )

  // part 2
  def solution2(input: Input): Int = {
    val ps = dijkstra2(input).get
    println(showMaze2(input, ps))
    ps.size
  }

  def dijkstra2(input: Input): Option[Set[Vec]] = {
    import input.*
    val startPos = Pos(start, initDir)
    val dist = mutable.Map[Pos, Int](startPos -> 0)
    val prev = mutable.Map[Pos, Set[Pos]]()

    def posDist(p: Pos): Dist = dist.get(p).map(Dist.Val.apply).getOrElse(Dist.Inf)

    val q = mutable.PriorityQueue[Pos](startPos)(using Ordering.by[Pos, Dist](posDist).reverse)
    val visited = mutable.Set[Pos]()

    @tailrec
    def go(): Option[Set[Vec]] = {
      // println("\ncall go()")
      // println(s"q: ${q.clone.dequeueAll}")
      // println(s"visited: $visited")
      // println(s"dist: $dist")
      // println(s"prev: $prev")
      if q.isEmpty then {
        val ends = prev.keys.filter(pos => pos.p == end).groupBy(dist.apply)
        val ps = ends(ends.keys.min)
        Some(traceBack(Queue().enqueueAll(ps), ps.map(_.p).toSet))
      } else {
        val cur = q.dequeue()
        // println(s"cur: $cur")
        if visited.contains(cur) then {
          // println("skip already visited")
          go()
        } else {
          visited += cur
          val curD = dist(cur)
          // println(s"dist(cur) = $curD")
          if cur.p == end then {
            // println(s"cur.p == end == $end so continue")
            go()
          } else {
            val ns = neighbours(cur)
              .filterNot { case (Pos(p, _), _) => maze.contains(p) }
            // println(s"neighbours: $ns")
            ns.foreach { (n, d) =>
              val newD = curD + d
              val oldD = dist.get(n)
              // println(s"neighbour ($n, $d). old dist = $oldD. new dist = $newD")
              if oldD.isEmpty || oldD.get >= newD then {
                // println(s"neighbour update")
                dist.put(n, newD)
                prev.updateWith(n)(_.map { ps =>
                  val res = ps.filter(p => dist(p) + (if p.p == n.p then rotCost else moveCost) == newD) + cur
                  // println(s"neighbour update prevs: $ps -> $res")
                  res
                }.orElse(Some(Set(cur))))
              }
            }
            q ++= ns.keys
            go()
          }
        }
      }
    }

    @tailrec
    def traceBack(q: Queue[Pos], acc: Set[Vec]): Set[Vec] =
      // println(s"call traceBack(q = $q, acc = $acc)")
      if q.isEmpty then acc
      else {
        val (cur, q1) = q.dequeue
        if cur == startPos then traceBack(q1, acc + cur.p)
        else traceBack(q1 ++ prev(cur), acc + cur.p)
      }

    go()
  }

  def showMaze2(input: Input, paths: Set[Vec]): String = {
    (0 to input.maze.map(_.y).max)
      .map { y =>
        (0 to input.maze.map(_.x).max).map { x =>
          val p = Vec(x, y)
          if input.maze.contains(p) then '#'
          else if input.start == p then 'S'
          else if input.end == p then 'E'
          else if paths.contains(p) then 'O'
          else '.'
        }.mkString
      }
      .mkString("\n")
  }
}
