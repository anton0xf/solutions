import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day19 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day19_linen_layout/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  case class Input(towels: List[String], designs: List[String])

  def parseInput(lines: IterableOnce[String]): Input = {
    val iter = lines.iterator
    val towels = iter.next().split(",\\s*").toList
    Input(towels, iter.filterNot(_.isBlank).toList)
  }

  case class Trie(end: Boolean, children: Map[Char, Trie]) {
    def put(s: String): Trie =
      if s.isEmpty then copy(end = true)
      else {
        val ch = s.head
        val s1 = s.tail
        copy(children = children.updatedWith(ch) {
          case None       => Some(Trie.empty.put(s1))
          case Some(trie) => Some(trie.put(s1))
        })
      }
  }

  object Trie {
    val empty: Trie = Trie(false, Map())

    def apply(ss: List[String]): Trie = {
      ss.foldLeft(empty) { (trie, s) => trie.put(s) }
    }
  }

  // part 1
  def solution1(input: Input): Int = {
    input.designs.count(checkDesign(Trie(input.towels)))
  }

  def checkDesign(trie: Trie)(design: String): Boolean = {
    def go(s: String, rest: Trie): Boolean = s.isEmpty || {
      val ch = s.head
      val s1 = s.tail
      (rest.end && go(s, trie)) || rest.children.get(ch).exists(go(s1, _))
    }
    go(design, trie)
  }

  // part 2
  def solution2(input: Input): Int = {
    input.designs.map(designOptions(Trie(input.towels))).sum
  }

  def designOptions(trie: Trie)(design: String): Int = {
    def go(s: String, rest: Trie): Int =
      if s.isEmpty then 1
      else {
        val ch = s.head
        val s1 = s.tail
        (if rest.end then go(s, trie) else 0) +
          rest.children.get(ch).map(go(s1, _)).getOrElse(0)
      }

    go(design, trie)
  }
}
