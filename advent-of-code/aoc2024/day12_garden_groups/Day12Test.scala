//> using target.scope test
import Day12.*
import scala.jdk.StreamConverters.*

class Day12Test extends munit.FunSuite {
  val input0: List[String] =
    """AB
      |BA""".stripMargin.lines().toScala(List)

  val input1: List[String] =
    """AAAA
      |BBCD
      |BBCC
      |EEEC""".stripMargin.lines().toScala(List)

  val input2: List[String] =
    """OOOOO
      |OXOXO
      |OOOOO
      |OXOXO
      |OOOOO""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input0.iterator), Input(Vector(Vector('A', 'B'), Vector('B', 'A'))))
  }

  test("regions") {
    assertEquals(
      regions(parseInput(input0.iterator)).toSet,
      Set(Set(Pos(0, 0)), Set(Pos(0, 1)), Set(Pos(1, 0)), Set(Pos(1, 1)))
    )
    assertEquals(
      regions(parseInput(input1.iterator)).toSet,
      Set(
        Set(Pos(0, 0), Pos(0, 1), Pos(0, 2), Pos(0, 3)),
        Set(Pos(1, 0), Pos(1, 1), Pos(2, 0), Pos(2, 1)),
        Set(Pos(1, 2), Pos(2, 2), Pos(2, 3), Pos(3, 3)),
        Set(Pos(1, 3)),
        Set(Pos(3, 0), Pos(3, 1), Pos(3, 2))
      )
    )
  }

  test("searchRegion") {
    assertEquals(searchRegion(Pos(0, 0), parseInput(input0.iterator)), Set(Pos(0, 0)))
    assertEquals(searchRegion(Pos(0, 1), parseInput(input0.iterator)), Set(Pos(0, 1)))
    assertEquals(searchRegion(Pos(1, 2), parseInput(input1.iterator)),
      Set(Pos(1, 2), Pos(2, 2), Pos(2, 3), Pos(3, 3)))
    assertEquals(searchRegion(Pos(2, 3), parseInput(input1.iterator)),
      Set(Pos(1, 2), Pos(2, 2), Pos(2, 3), Pos(3, 3)))
    assertEquals(searchRegion(Pos(1, 0), parseInput(input1.iterator)),
      Set(Pos(1, 0), Pos(1, 1), Pos(2, 0), Pos(2, 1)))
  }

  test("regionPerimeter") {
    assertEquals(regionPerimeter(Set(Pos(1, 2), Pos(2, 2), Pos(2, 3), Pos(3, 3))), 10)
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input0.iterator)), BigInt(16))
    assertEquals(solution1(parseInput(input1.iterator)), BigInt(140))
    assertEquals(solution1(parseInput(input2.iterator)), BigInt(772))
  }

  // part 2
}
