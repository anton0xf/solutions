import Day15.Obj.Box

import scala.annotation.{tailrec, targetName}
import scala.collection.immutable
import scala.collection.immutable.Queue
import scala.util.Using
import scala.io.Source

object Day15 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day15_warehouse_woes/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  case class Input(
      /** warehouse map */
      map: Map[Vec, Obj],
      /** robot position */
      p: Vec,
      /** movement commands list */
      cmds: List[Vec]
  )

  case class Vec(x: Int, y: Int) {
    @targetName("plus")
    def +(p: Vec): Vec = Vec(x + p.x, y + p.y)
    def incX: Vec = Vec(x + 1, y)
    def decX: Vec = Vec(x - 1, y)
    def doubleX: Vec = Vec(x * 2, y)

    def gps: Int = x + y * 100
  }

  enum Obj { case Box, Wall }

  val dirs = Map('>' -> Vec(1, 0), 'v' -> Vec(0, 1), '<' -> Vec(-1, 0), '^' -> Vec(0, -1))

  def parseInput(lines: IterableOnce[String]): Input = {
    val (mapLines, commandLines) = lines.iterator.span(!_.isBlank)
    val (map, p) = parseMap(mapLines)
    val cmds = commandLines.drop(1).flatMap(_.map(dirs.apply)).toList
    Input(map = map, p = p, cmds = cmds)
  }

  def parseMap(lines: IterableOnce[String]): (Map[Vec, Obj], Vec) = {
    val ps = (for {
      (line, y) <- lines.iterator.zipWithIndex
      (ch, x) <- line.zipWithIndex
      if ch != '.'
    } yield Vec(x, y) -> (ch match
      case '#' => Left(Obj.Wall)
      case 'O' => Left(Obj.Box)
      case '@' => Right(())
    )).toList
    val map = ps.flatMap((p, x) => x.swap.toOption.map(p -> _)).toMap
    val robot = ps.find(_._2.isRight).get._1
    (map, robot)
  }

  // part 1
  def solution1(input: Input): Int = {
    val end = simulate(input)
    end.map.iterator.map((p, x) => if x == Obj.Box then p.gps else 0).sum
  }

  @tailrec
  def simulate(data: Input): Input = data.cmds match
    case Nil => data
    case cmd :: cmds =>
      val (p, map) = step(cmd, data.p, data.map)
      simulate(Input(map, p, cmds))

  def step(cmd: Vec, p: Vec, map: Map[Vec, Obj]): (Vec, Map[Vec, Obj]) = {
    val next = p + cmd
    map.get(next) match
      case None           => (next, map)
      case Some(Obj.Wall) => (p, map)
      case Some(Obj.Box) =>
        val next2 = LazyList.iterate(next)(_ + cmd).find(!map.get(_).contains(Obj.Box)).get
        map.get(next2) match
          case None           => (next, move(map)(next, next2))
          case Some(Obj.Wall) => (p, map)
          case Some(Obj.Box)  => throw new Exception(s"unexpected Box at $next2")
  }

  def move(map: Map[Vec, Obj])(p0: Vec, p1: Vec): Map[Vec, Obj] =
    val x = map(p0)
    map.removed(p0).updated(p1, x)

  // part 2

  enum Obj2 { case BoxL, BoxR, Wall }
  case class State2(
      /** robot position */
      p: Vec,
      /** warehouse map */
      map: Map[Vec, Obj2]
  ) {
    def show: String = (0 to map.keys.map(_.y).max)
      .map { y =>
        (0 to map.keys.map(_.x).max).map { x =>
          val pos = Vec(x, y)
          map.get(pos) match
            case None            => if pos == p then '@' else '.'
            case Some(Obj2.Wall) => '#'
            case Some(Obj2.BoxL) => '['
            case Some(Obj2.BoxR) => ']'
        }.mkString
      }
      .mkString("\n")
  }

  def solution2(input: Input): Int = {
    val state = toState2(input)
    val end = simulate2(input.cmds, state)
    end.map.iterator.map((p, x) => if x == Obj2.BoxL then p.gps else 0).sum
  }

  def toState2(input: Input) = State2(
    input.p.doubleX,
    input.map.flatMap((p, x) =>
      Seq(p.doubleX, p.doubleX.incX) zip (x match
        case Obj.Wall => Seq(Obj2.Wall, Obj2.Wall)
        case Obj.Box  => Seq(Obj2.BoxL, Obj2.BoxR)
      )
    )
  )

  @tailrec
  def simulate2(cmds: List[Vec], state: State2): State2 = cmds match
    case Nil         => state
    case cmd :: cmds => simulate2(cmds, step2(cmd, state))

  def step2(cmd: Vec, state: State2): State2 = {
    val next = state.p + cmd
    state.map.get(next) match
      case None            => state.copy(p = next)
      case Some(Obj2.Wall) => state
      case Some(_) =>
        findMovableCluster(cmd, next, state.map) match
          case None          => state
          case Some(cluster) => State2(next, move2(cmd, state.map)(cluster))
  }

  def findMovableCluster(cmd: Vec, start: Vec, map: Map[Vec, Obj2]): Option[List[(Vec, Obj2)]] = {
    @tailrec
    def go(q: Queue[Vec], cluster: List[(Vec, Obj2)]): Option[List[(Vec, Obj2)]] = {
      if q.isEmpty then Some(cluster)
      else {
        val (p, q1) = q.dequeue
        map.get(p) match
          case None            => go(q1, cluster)
          case Some(Obj2.Wall) => None
          case Some(Obj2.BoxL) =>
            val pair = p.incX
            assert(map.get(pair).contains(Obj2.BoxR))
            val next =
              if cmd.y != 0
              then Seq(p, pair).map(_ + cmd)
              else { assert(cmd.x == 1); Seq(pair.incX) }
            go(q1 :++ next, (p -> Obj2.BoxL) :: (pair -> Obj2.BoxR) :: cluster)
          case Some(Obj2.BoxR) =>
            val pair = p.decX
            assert(map.get(pair).contains(Obj2.BoxL))
            val next =
              if cmd.y != 0
              then Seq(p, pair).map(_ + cmd)
              else { assert(cmd.x == -1); Seq(pair.decX) }
            go(q1 :++ next, (pair -> Obj2.BoxL) :: (p -> Obj2.BoxR) :: cluster)
      }
    }
    go(Queue(start), Nil)
  }

  def move2(cmd: Vec, map: Map[Vec, Obj2])(cluster: List[(Vec, Obj2)]): Map[Vec, Obj2] =
    map -- cluster.map(_._1) ++ cluster.map((p, x) => (p + cmd, x))

  def parseMap2(lines: IterableOnce[String]): State2 = {
    val ps = (for {
      (line, y) <- lines.iterator.zipWithIndex
      (ch, x) <- line.zipWithIndex
      if ch != '.'
    } yield Vec(x, y) -> (ch match
      case '#' => Left(Obj2.Wall)
      case '[' => Left(Obj2.BoxL)
      case ']' => Left(Obj2.BoxR)
      case '@' => Right(())
    )).toList
    val map = ps.flatMap((p, x) => x.swap.toOption.map(p -> _)).toMap
    val robot = ps.find(_._2.isRight).get._1
    State2(robot, map)
  }
}
