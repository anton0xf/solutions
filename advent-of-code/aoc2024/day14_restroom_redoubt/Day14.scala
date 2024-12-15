import scala.annotation.targetName
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day14 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day14_restroom_redoubt/input")) { source =>
      val input = parseInput(source.getLines())
      val size = Vec(101, 103)
      println(s"part 1: ${solution1(input, size)}")
      println(s"part 2: ${solution2(input, size)}")
    }
  }

  type Input = List[Robot]
  case class Robot(p: Vec, v: Vec)
  case class Vec(x: Int, y: Int) {
    @targetName("plus")
    def +(p: Vec): Vec = Vec(x + p.x, y + p.y)

    @targetName("mult")
    def *(n: Int): Vec = Vec(x * n, y * n)

    @targetName("mod")
    def %(size: Vec): Vec = Vec(mod(x, size.x), mod(y, size.y))
  }

  def mod(a: Int, b: Int): Int =
    val m = a % b
    if m < 0 then m + b else m

  def parseInput(lines: IterableOnce[String]): Input = lines.iterator.map(parseRobot).toList

  // p=0,4 v=3,-3
  def parseRobot(line: String): Robot = line.split(' ').map(_.split('=')) match
    case Array(Array("p", p), Array("v", v)) => Robot(parseVec(p), parseVec(v))
    case _ => throw new Exception(s"unexpected line format: $line")

  def parseVec(str: String): Vec = str.split(',').map(_.toInt) match
    case Array(x, y) => Vec(x, y)
    case _           => throw new Exception(s"unexpected Vec format: $str")

  // part 1
  def solution1(input: Input, size: Vec): Int = {
    simulate(input, size, 100).toList
      .flatMap { (p, n) => quadrant(size)(p).map((_, n)) }
      .groupMapReduce(_._1)(_._2)(_ + _)
      .values
      .product
  }

  def simulate(input: Input, size: Vec, n: Int): Map[Vec, Int] = input
    .map { case Robot(p, v) => (p + v * n) % size }
    .groupMapReduce(identity)(_ => 1)(_ + _)

  def quadrant(size: Vec)(p: Vec): Option[(Int, Int)] = {
    val mx = size.x / 2
    val my = size.y / 2
    if p.x == mx || p.y == my then None
    else Some((p.x / (mx + 1), p.y / (my + 1)))
  }

  // part 2
  def solution2(input: Input, size: Vec): Int = {
    val (n, m) = LazyList
      .from(0)
      .map(n => (n, simulate(input, size, n)))
      .find { (n, m) => m.values.forall(_ == 1) }
      .get
    println(visualize(size, m))
    n
  }

  def visualize(size: Vec, m: Map[Vec, Int]): String = {
    (0 until size.y)
      .map { y =>
        (0 until size.x).map { x =>
          m.get(Vec(x, y)).map(_.toString).getOrElse('.')
        }.mkString
      }
      .mkString("\n")
  }
}
