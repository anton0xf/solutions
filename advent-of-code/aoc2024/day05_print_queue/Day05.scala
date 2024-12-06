import scala.util.Using
import scala.io.Source

object Day05 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day05_print_queue/input")) { source =>
      val input: Input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  case class Input(rules: Set[Rule], updates: List[Update])
  case class Rule(left: Int, right: Int)
  case class Update(pages: Vector[Int])

  def parseInput(lines: Iterator[String]): Input = {
    val (ruleLines, updateLines) = lines.span(line => line.nonEmpty)
    val rules = ruleLines.map(parseRule).toSet
    val updates = updateLines.drop(1).map(parseUpdates).toList
    Input(rules, updates)
  }

  private def parseRule(line: String): Rule = line.split('|').map(_.toIntOption) match {
    case Array(Some(left), Some(right)) => Rule(left, right)
    case _                              => throw Exception(s"unexpected rule format: $line")
  }

  private def parseUpdates(line: String): Update = Update(line.split(',').map(_.toInt).toVector)

  // part 1
  def solution1(input: Input): Int = input.updates
    .filter(rightOrder(input.rules))
    .map(update => getMid(update.pages))
    .sum

  def rightOrder(rules: Iterable[Rule])(update: Update): Boolean = {
    // map page number to its index in list
    val m = update.pages.zipWithIndex.toMap
    rules.forall(rule =>
      List(rule.left, rule.right).flatMap(m.get) match {
        case List(leftIdx, rightIdx) => leftIdx < rightIdx
        case _                       => true
      }
    )
  }

  def getMid(pages: Vector[Int]): Int = {
    assert(pages.size % 2 == 1)
    pages(pages.size / 2)
  }

  // part 2
  def solution2(input: Input): Int = input.updates
    .filter(update => !rightOrder(input.rules)(update))
    .map(update => fixOrder(input.rules)(update.pages))
    .map(getMid)
    .sum

  def fixOrder(rules: Set[Rule])(pages: Vector[Int]): Vector[Int] =
    pages.sortWith { (x, y) => rules.contains(Rule(x, y))}
}
