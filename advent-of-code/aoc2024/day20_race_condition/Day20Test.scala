//> using target.scope test
import Day20.*
import scala.jdk.StreamConverters.*

class Day20Test extends munit.FunSuite {
  val input0: List[String] =
    """####
      |#E.#
      |##.#
      |#S.#
      |####""".stripMargin.lines().toScala(List)

  val input1: List[String] =
    """###############
      |#...#...#.....#
      |#.#.#.#.#.###.#
      |#S#...#.#.#...#
      |#######.#.#.###
      |#######.#.#...#
      |#######.#.###.#
      |###..E#...#...#
      |###.#######.###
      |#...###...#...#
      |#.#####.#.###.#
      |#.#...#.#.#...#
      |#.#.#.#.#.#.###
      |#...#...#...###
      |###############""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(
      parseInput(input0),
      Track(Vec(1, 3), Vec(1, 1), Set(Vec(2, 1), Vec(2, 2), Vec(2, 3)), (4, 5))
    )
  }

  // part 1
  test("solution1 0") {
    assertEquals(solution1(parseInput(input0), 0), 3)
    assertEquals(solution1(parseInput(input0), 1), 1)
    assertEquals(solution1(parseInput(input0), 2), 1)
    assertEquals(solution1(parseInput(input0), 3), 0)
  }

  test("solution1 1") {
    assertEquals(solution1(parseInput(input1), 64), 1)
  }

  // part 2
}
