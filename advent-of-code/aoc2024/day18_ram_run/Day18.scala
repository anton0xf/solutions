import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day18 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day18_ram_run/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
    }
  }

  case class Input(lines: List[String])

  def parseInput(lines: IterableOnce[String]): Input = Input(lines.iterator.toList)

  // part 1
  def solution1(input: Input): Int = {
    // println(input)
    input.lines.size
  }

  // part 2
}
