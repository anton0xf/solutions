import scala.util.Using
import scala.io.Source

object Day07 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day07_bridge_repair/input")) { source =>
      val input = source.getLines().map(parseEq).toList
      val res1 = solution1(input)
      println(s"part 1: $res1")
    }
  }

  def parseEq(line: String): Eq = line.split(": ") match {
    case Array(res, args) => Eq(BigInt(res), args.split(' ').map(BigInt.apply).toList)
    case _                => throw new Exception(s"Unexpected format of equation: $line")
  }

  type Input = List[Eq]
  case class Eq(res: BigInt, args: List[BigInt])

  // part 1
  def solution1(input: Input): BigInt = input.flatMap(solveEq).sum
  def solveEq(eq: Eq): Option[BigInt] = {
    def go(target: BigInt, args: List[BigInt]): Option[BigInt] = {
      args match
        case Nil => None
        case List(x) => if target == x then Some(eq.res) else None
        case x :: xs =>
          go(target - x, xs).orElse {
            if target % x == 0 then go(target / x, xs) else None
          }
    }
    go(eq.res , eq.args.reverse)
  }
}
