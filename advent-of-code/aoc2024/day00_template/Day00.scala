import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day00 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day00_template/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
    }
  }

  case class Input(lines: List[String])

  def parseInput(lines: Iterator[String]): Input = Input(lines.toList)

  // part 1
  def solution1(input: Input): Int = {
    input.lines.foreach(println) // TODO remove
    input.lines.size
  }

  // part 2
}