import Day15.Obj.Box

import scala.annotation.targetName
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day15 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day15_warehouse_woes/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
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
    end.map.iterator.map((p, x) => if x == Box then p.gps else 0).sum
  }

  def simulate(data: Input): Input = data.cmds match
    case Nil => data
    case cmd :: cmds =>
      val (p, map) = step(cmd, data.p, data.map)
      simulate(Input(map, p, cmds))

  def step(cmd: Vec, p: Vec, map: Map[Vec, Obj]): (Vec, Map[Vec, Obj]) = {
    val next = p + cmd
    val x = map.get(next)
    x match
      case None => (next, map)
      case Some(Obj.Wall) => (p, map)
      case Some(Obj.Box) =>
        val next2 = LazyList.iterate(next)(_ + cmd).find(!map.get(_).contains(Obj.Box)).get
        map.get(next2) match
          case None => (next, move(map)(next, next2))
          case Some(Obj.Wall) => (p, map)
          case Some(Obj.Box) => throw new Exception(s"unexpected Box at $next2")
  }

  def move(map: Map[Vec, Obj])(p0: Vec, p1: Vec): Map[Vec, Obj] =
    val x = map(p0)
    map.removed(p0).updated(p1, x)

  // part 2
}
