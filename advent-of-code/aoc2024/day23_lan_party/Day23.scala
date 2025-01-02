import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day23 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day23_lan_party/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"input size: ${input.size}")
      println(s"part 1: ${solution1(input)}")
    }
  }

  type Input = List[(String, String)]

  def parseInput(lines: IterableOnce[String]): Input =
    lines.iterator.filterNot(_.isBlank).map(line => line.split('-')).map { case Array(a, b) => (a, b) }.toList

  // part 1
  def solution1(input: Input): Int = {
    val edges = input.map { case (a, b) => Set(a, b) }.toSet
    def addTo(a: String, b: String, g: Map[String, Set[String]]): Map[String, Set[String]] = g.updatedWith(a) {
      case None    => Some(Set(b))
      case Some(s) => Some(s + b)
    }
    val graph = edges.foldLeft(Map[String, Set[String]]()) { (g, e) =>
      e.toList match {
        case List(a, b) => addTo(b, a, addTo(a, b, g))
        case _          => throw new Exception(s"unexpected edge $e")
      }
    }
    val triples = edges.flatMap { e =>
      e.toList match {
        case List(a, b) => graph(a).withFilter { c => c != b && graph(b).contains(c) }.map { c => Set(a, b, c) }
        case _          => throw new Exception(s"unexpected edge $e")
      }
    }
    triples.count(_.exists(_.startsWith("t")))
  }

  // part 2
}
