import scala.util.Using
import scala.io.Source
import scala.util.matching.Regex

object Day03 {
  val re: Regex = "mul\\((\\d{1,3}),(\\d{1,3})\\)".r

  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day03_mull_it_over/input")) { source =>
      val input = source.getLines().mkString("\n")
      // val reports = lines.map(_.split("\\s+").map(_.toInt).toList).toList
      val muls = for { m <- re.findAllMatchIn(input) }
        yield (BigInt(m.group(1)), BigInt(m.group(2)))
      val res1 = muls.map((x,y) => x * y).sum
      println(s"part 1: $res1")
    }
  }
}
