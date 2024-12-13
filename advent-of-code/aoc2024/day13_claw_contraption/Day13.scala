import java.io.Reader
import scala.annotation.tailrec
import scala.collection.immutable
import scala.util.Using
import scala.io.Source
import scala.util.parsing.combinator.*

object Day13 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day13_claw_contraption/input")) { source =>
      val data = InputParser.parseData(source.bufferedReader())
      println(s"collinear buttons: ${data.machines.count(isCollinear)}")
      println(s"part 1: ${solution1(data)}")
    }
  }

  case class Data(machines: List[Machine])
  case class Machine(a: Vec, b: Vec, prize: Vec)
  case class Vec(x: Int, y: Int)

  object InputParser extends RegexParsers {
    def sep: Parser[Any] = '\n'
    def num: Parser[Int] = """\d+""".r ^^ (_.toInt)
    def button(ch: Char): Parser[Vec] =
      ("Button " + ch + ": X+") ~> num ~ (", Y+" ~> num <~ """\n?""".r) ^^ { case x ~ y =>
        Vec(x, y)
      }
    def prize: Parser[Vec] = "Prize: X=" ~> num ~ (", Y=" ~> num) ^^ { case x ~ y => Vec(x, y) }
    def machine: Parser[Machine] = button('A') ~ button('B') ~ prize ^^ { case a ~ b ~ prize =>
      Machine(a, b, prize)
    }
    def data: Parser[Data] = rep1sep(machine, sep) ^^ { Data.apply }

    def parseData(in: Reader): Data = parse(data, in).get
  }

  def isCollinear(machine: Machine): Boolean =
    import machine.*
    a.x * b.y == a.y * b.x

  // part 1
  def solution1(data: Data): Int = {
    data.machines.flatMap(solve).map { case Vec(a, b) => a * 3 + b }.sum
  }

  def solve(machine: Machine): Option[Vec] = {
    import machine.*
    // a.x * na + b.x * nb = prize.x
    // a.y * na + b.y * nb = prize.y
    val gcdB = gcd(b.x, b.y)
    val bx = b.x / gcdB
    val by = b.y / gcdB
    val a1 = prize.x * by - prize.y * bx
    val a2 = a.x * by - a.y * bx
    if a1 % a2 != 0 then None
    else {
      val na = a1 / a2
      val b1 = prize.x - a.x * na
      if b1 % b.x != 0 then None
      else Some(Vec(na, b1 / b.x))
    }
  }

  @tailrec
  def gcd(a: Int, b: Int): Int = {
    if b == 0 then a else gcd(b, a % b)
  }

  // part 2
}
