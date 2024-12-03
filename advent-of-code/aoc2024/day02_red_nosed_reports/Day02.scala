import scala.util.Using
import scala.io.Source

object Day02 {
  def diff(xs: List[Int]): List[Int] = (xs.tail zip xs.dropRight(1)).map(_ - _)
  def inRange(x: Int): Boolean = (1 to 3).contains(x)
  def isInc(xs: List[Int]): Boolean = diff(xs).forall(inRange)
  def isDec(xs: List[Int]): Boolean = diff(xs).map(-_).forall(inRange)
  def isSafe(report: List[Int]): Boolean = isInc(report) || isDec(report)

  def isInc2(xs: List[Int]): Boolean = {
    def go(xs: List[Int], allowSkip: Boolean): Boolean = xs match {
      case x1 :: x2 :: xs =>
        (inRange(x2 - x1) && go(x2 :: xs, allowSkip)) ||
          (allowSkip && go(x1 :: xs, false))
      case _ => true
    }
    go(xs, true) || go(xs.tail, false)
  }
  def isDec2(xs: List[Int]): Boolean = isInc2(xs.map(-_))
  def isSafe2(report: List[Int]): Boolean = isInc2(report) || isDec2(report)

  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day02_red_nosed_reports/input")) { source =>
      val lines = source.getLines()
      val reports = lines.map(_.split("\\s+").map(_.toInt).toList).toList
      val res1 = reports.count(report => isSafe(report))
      println(s"part 1: $res1")
      val res2 = reports.count(report => isSafe2(report))
      println(s"part 2: $res2")
    }
  }
}
