//> using target.scope test
import Day10.*
import scala.jdk.StreamConverters.*

class Day10Test extends munit.FunSuite {
  val input0: List[String] =
    """012345
      |..9876""".stripMargin.lines().toScala(List)

  val input1: List[String] =
    """0123
      |1234
      |8765
      |9876""".stripMargin.lines().toScala(List)

  val input2: List[String] =
    """89010123
      |78121874
      |87430965
      |96549874
      |45678903
      |32019012
      |01329801
      |10456732""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(
      parseInput(input0.iterator),
      Input(Vector(Vector(0, 1, 2, 3, 4, 5), Vector(-1, -1, 9, 8, 7, 6)))
    )
  }

  test("Input.findPos") {
    assertEquals(parseInput(input0.iterator).findPos(9), List(Pos(1, 2)))
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input0.iterator)), 1)
    assertEquals(solution1(parseInput(input1.iterator)), 1)
    assertEquals(solution1(parseInput(input2.iterator)), 36)
  }

  // part 2
}
