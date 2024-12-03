import scala.util.Using
import scala.io.Source

object Day01 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day01_historian_hysteria/input")) { source =>
      val lines = source.getLines()
      val pairs = lines.map(_.split("\\s+").map(_.toInt).toList).toList
      val (xs: List[Int], ys: List[Int]) = pairs.unzip {
        case List(a, b) => (a, b)
        case line => throw Exception(s"unexpected line: $line")
      }
      val xss = xs.sorted
      val yss = ys.sorted
      val ps = xss.zip(yss)
      val res1 = ps.map { (x, y) => (x - y).abs }.sum
      println(s"part 1: $res1")

      val ym = yss.groupBy(identity)
      val res2 = xss.map { x => ym.get(x).map(ys => BigInt(x) * ys.size).getOrElse(BigInt(0)) }.sum
      println(s"part 2: $res2")
    }
  }
}