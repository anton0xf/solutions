import scala.util.Using
import scala.io.Source
import scala.util.matching.Regex

object Day03 {
  val re1: Regex = """mul\((\d{1,3}),(\d{1,3})\)""".r
  val re2: Regex = """(do)\(\)|(don't)\(\)|(mul)\((\d{1,3}),(\d{1,3})\)""".r

  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day03_mull_it_over/input")) { source =>
      val input = source.getLines().mkString("\n")
      // part 1
      val res1 = solution1(input)
      println(s"part 1: $res1")

      // part 2
      val res2 = solution2(input)
      println(s"part 2: $res2")
    }
  }

  def solution1(input: String): BigInt = {
    val muls = for {
      m <- re1.findAllMatchIn(input)
    } yield (BigInt(m.group(1)), BigInt(m.group(2)))
    muls.map((x, y) => x * y).sum
  }

  private enum Command {
    case Do(flag: Boolean)
    case Mul(x: BigInt, y: BigInt)
  }
  import Day03.Command.*

  def solution2(input: String): BigInt = {
    val commands = for {
      m <- re2.findAllMatchIn(input)
    } yield getCommand2(m)
    commands.foldLeft(EvalState(true, 0))(eval).sum
  }

  private def getCommand2(m: Regex.Match): Command = {
    (m.group(1), m.group(2), m.group(3), m.group(4), m.group(5)) match {
      case ("do", null, null, null, null)    => Do(true)
      case (null, "don't", null, null, null) => Do(false)
      case (null, null, "mul", s1, s2)       => Mul(BigInt(s1), BigInt(s2))
    }
  }

  private case class EvalState(mulEnabled: Boolean, sum: BigInt)

  private def eval(state: EvalState, command: Command) = {
    command match {
      case Do(flag) => state.copy(mulEnabled = flag)
      case Mul(x, y) =>
        if state.mulEnabled
        then state.copy(sum = state.sum + (x * y))
        else state
    }
  }
}
