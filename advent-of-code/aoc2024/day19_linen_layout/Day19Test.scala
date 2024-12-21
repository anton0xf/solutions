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
    assertEquals(solution2(parseInput(input1)), BigInt(16))
  }

  val towels1: List[String] = List("r", "wr", "b", "g", "bwu", "rb", "gb", "br")

  test("designOptions") {
    val f = designOptions(Trie(towels1))
    assertEquals(f("brwrr").toInt, 2)
    assertEquals(f("bggr").toInt, 1)
    assertEquals(f("gbbr").toInt, 4)
    assertEquals(f("rrbgbr").toInt, 6)
    assertEquals(f("bwurrg").toInt, 1)
    assertEquals(f("brgr").toInt, 2)
    assertEquals(f("ubwu").toInt, 0)
    assertEquals(f("bbrgwb").toInt, 0)
    assertEquals(f("rbr").toInt, 3)
    assertEquals(f("rbrwrrbr").toInt, 9)
    assertEquals(f("rbrwrrbrww").toInt, 0)
  }

  test("designOptions2") {
    val f = designOptions2(towels1)
    assertEquals(f("brwrr").toInt, 2)
    assertEquals(f("bggr").toInt, 1)
    assertEquals(f("gbbr").toInt, 4)
    assertEquals(f("rrbgbr").toInt, 6)
    assertEquals(f("bwurrg").toInt, 1)
    assertEquals(f("brgr").toInt, 2)
    assertEquals(f("ubwu").toInt, 0)
    assertEquals(f("bbrgwb").toInt, 0)
    assertEquals(f("rbr").toInt, 3)
    assertEquals(f("rbrwrrbr").toInt, 9)
    assertEquals(f("rbrwrrbrww").toInt, 0)
  }

  test("designOptions == designOptions2") {
    val towels = List("r", "wuu", "bu", "buru")
    val f = designOptions(Trie(towels))
    val f2 = designOptions2(towels)
    def check(s: String): Unit =
      assertEquals(f(s), f2(s))
    check("wuubur")
  }

}
