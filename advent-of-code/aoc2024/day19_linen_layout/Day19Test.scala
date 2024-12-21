//> using target.scope test
import Day19.*
import scala.jdk.StreamConverters.*

class Day19Test extends munit.FunSuite {
  val input0: List[String] =
    """r, wr, b
      |
      |brwrr
      |bggr
      """.stripMargin.lines().toScala(List)
  val input1: List[String] =
    """r, wr, b, g, bwu, rb, gb, br
      |
      |brwrr
      |bggr
      |gbbr
      |rrbgbr
      |ubwu
      |bwurrg
      |brgr
      |bbrgwb""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input0), Input(List("r", "wr", "b"), List("brwrr", "bggr")))
  }

  test("Trie") {
    assertEquals(
      Trie(List("ab")),
      Trie(false, Map('a' -> Trie(false, Map('b' -> Trie(true, Map())))))
    )
    assertEquals(
      Trie(List("abc", "a")),
      Trie(false, Map('a' -> Trie(true, Map('b' -> Trie(false, Map('c' -> Trie(true, Map())))))))
    )
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input1)), 6)
  }

  // part 2
  test("solution2") {
    assertEquals(solution2(parseInput(input1)), 16)
  }
}
