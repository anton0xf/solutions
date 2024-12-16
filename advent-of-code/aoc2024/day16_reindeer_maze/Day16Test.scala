//> using target.scope test
import Day16.*
import scala.jdk.StreamConverters.*

class Day16Test extends munit.FunSuite {
  val input0: List[String] =
    """####
      |#.E#
      |#S.#
      |####""".stripMargin.lines().toScala(List)

  val input1: List[String] =
    """###############
      |#.......#....E#
      |#.#.###.#.###.#
      |#.....#.#...#.#
      |#.###.#####.#.#
      |#.#.#.......#.#
      |#.#.#####.###.#
      |#...........#.#
      |###.#.#####.#.#
      |#...#.....#.#.#
      |#.#.#.###.#.#.#
      |#.....#...#.#.#
      |#.###.#.#.#.#.#
      |#S..#.....#...#
      |###############""".stripMargin.lines().toScala(List)

  test("parseInput") {
    val data = parseInput(input0)
    assertEquals(data.start, Vec(1, 2))
    assertEquals(data.end, Vec(2, 1))
    assertEquals(showMaze(data, Nil), input0.mkString("\n"))
  }

  test("solution1") {
    assertEquals(solution1(parseInput(input0)), 1002)
    assertEquals(solution1(parseInput(input1)), 7036)
  }

  val input3: List[String] =
    """#####
      |#..E#
      |#S.##
      |#####""".stripMargin.lines().toScala(List)

  test("solution2") {
    assertEquals(solution2(parseInput(input0)), 3)
    assertEquals(solution2(parseInput(input3)), 5)
    assertEquals(solution2(parseInput(input1)), 45)
  }

//  test("solution2_3") {
//    assertEquals(solution2(parseInput(input3)), 5)
//  }
}
