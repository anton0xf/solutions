//> using target.scope test
import Day21.*
import scala.jdk.StreamConverters.*

class Day21Test extends munit.FunSuite {
  val input: List[String] =
    """029A
      |980A
      |179A
      |456A
      |379A""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input), List("029A", "980A", "179A", "456A", "379A"))
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input)), 126384)
  }

  test("complexity") {
    assertEquals(complexity("029A"), 68 * 29)
    assertEquals(complexity("980A"), 60 * 980)
    assertEquals(complexity("179A"), 68 * 179)
    assertEquals(complexity("456A"), 64 * 456)
    assertEquals(complexity("379A"), 64 * 379)
  }

  test("typeIndirect") {
    assertEquals(typeIndirect("029A").head.length, 68)
    assertEquals(typeIndirect("980A").head.length, 60)
    assertEquals(typeIndirect("179A").head.length, 68)
    assertEquals(typeIndirect("456A").head.length, 64)
    assertEquals(typeIndirect("379A").head.length, 64)
  }

  test("simulate") {
    assertEquals(simulate("<A^A>^^AvvvA", numpad), Some("029A"))
    assertEquals(simulate("<A^A^>^AvvvA", numpad), Some("029A"))
    assertEquals(simulate("<A^A^^>AvvvA", numpad), Some("029A"))
    assertEquals(simulate("<<", numpad), None)
    assertEquals(simulate("<<A", numpad), None)
    assertEquals(simulate("v<<A>>^A<A>AvA<^AA>A<vAAA>^A", dirpad), Some("<A^A>^^AvvvA"))
    assertEquals(
      simulate("<vA<AA>>^AvAA<^A>A<v<A>>^AvA^A<vA>^A<v<A>^A>AAvA^A<v<A>A>^AAAvA<^A>A", dirpad),
      Some("v<<A>>^A<A>AvA<^AA>A<vAAA>^A")
    )
  }

  test("typeString") {
    assertEquals(typeString("029A", numpad).toSet, Set("<A^A>^^AvvvA", "<A^A^^>AvvvA"))
  }

  test("typeChar") {
    assertEquals(typeChar('0', Vec(3, 2), numpad), List("<A".toVector))
    assertEquals(typeChar('5', Vec(3, 2), numpad).toSet, List("<^^A", "^^<A").map(_.toVector).toSet)
    assertEquals(typeChar('1', Vec(3, 2), numpad), List("^<<A".toVector))
    assertEquals(typeChar('0', Vec(2, 0), numpad), List(">vA".toVector))
  }

  // part 2
}
