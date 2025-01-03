import scala.annotation.tailrec
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day23 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day23_lan_party/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"input size: ${input.size}")
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  type Input = List[(String, String)]

  def parseInput(lines: IterableOnce[String]): Input =
    lines.iterator.filterNot(_.isBlank).map(line => line.split('-')).map { case Array(a, b) => (a, b) }.toList

  // part 1
  def solution1(input: Input): Int = {
    val edges = toEdgesSet(input)
    val graph = edgesToGraph(edges)
    val triples = edges.flatMap { e =>
      e.toList match {
        case List(a, b) => graph(a).withFilter { c => c != b && graph(b).contains(c) }.map { c => Set(a, b, c) }
        case _          => throw new Exception(s"unexpected edge $e")
      }
    }
    triples.count(_.exists(_.startsWith("t")))
  }

  private def toEdgesSet(input: Input) = input.map { case (a, b) => Set(a, b) }.toSet

  private def edgesToGraph(edges: Set[Set[String]]): Map[String, Set[String]] = {
    def addTo(a: String, b: String, g: Map[String, Set[String]]): Map[String, Set[String]] = g.updatedWith(a) {
      case None    => Some(Set(b))
      case Some(s) => Some(s + b)
    }
    edges.foldLeft(Map[String, Set[String]]()) { (g, e) =>
      e.toList match {
        case List(a, b) => addTo(b, a, addTo(a, b, g))
        case _          => throw new Exception(s"unexpected edge $e")
      }
    }
  }

  // part 2
  def solution2(input: Input): String = {
    val graph = edgesToGraph(toEdgesSet(input))
    val cliques = bronKerbosch(graph)
    cliques.maxBy(_.size).toVector.sorted.mkString(",")
  }

  def bronKerbosch(graph: Map[String, Set[String]]): Set[Set[String]] = {
    def go(r: Set[String], p: Set[String], x: Set[String]): Set[Set[String]] =
      if p.isEmpty && x.isEmpty then Set(r) else loop(r, p, x, Set())

    @tailrec
    def loop(r: Set[String], p: Set[String], x: Set[String], acc: Set[Set[String]]): Set[Set[String]] = {
      if p.isEmpty then acc
      else {
        val v = p.head
        val acc1 = acc ++ go(r + v, p intersect graph(v), x intersect graph(v))
        loop(r, p - v, x + v, acc1)
      }
    }

    go(Set(), graph.keySet, Set())
  }
}
