//> using target.scope test
import Day06.*
import scala.jdk.StreamConverters.*

class Day06Test extends munit.FunSuite {
  val input0 = """
    |..#.
    |..^.
    |""".stripMargin.lines().toScala(List)
  val input1 = """
    |....#.....
    |.........#
    |..........
    |..#.......
    |.......#..
    |..........
    |.#..^.....
    |........#.
    |#.........
    |......#...
    |""".stripMargin.lines().toScala(List)
  test("parseInput") {
    assertEquals(
      parseInput(input0.iterator),
      Input(size = (2, 4), start = Pos(1, 2), obstructions = Set(Pos(0, 2)))
    )
    assertEquals(
      parseInput(input1.iterator),
      Input(
        size = (10, 10),
        start = Pos(6, 4),
        obstructions = Set(
          Pos(0, 4),
          Pos(8, 0),
          Pos(9, 6),
          Pos(1, 9),
          Pos(4, 7),
          Pos(7, 8),
          Pos(6, 1),
          Pos(3, 2)
        )
      )
    )
  }
  test("solution1") {
    assertEquals(solution1(parseInput(input0.iterator)), 2)
    assertEquals(solution1(parseInput(input1.iterator)), 41)
  }
  test("solution2") {
    assertEquals(solution2(parseInput(input0.iterator)), 0)
    assertEquals(solution2(parseInput(input1.iterator)), 6)
  }
}
