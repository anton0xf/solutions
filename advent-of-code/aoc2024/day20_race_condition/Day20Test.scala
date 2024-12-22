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
    // cheats: Vec(7,7) -> HashSet(Vec(5,7))
  }

  // part 2
  test("circle") {
    assertEquals(Vec(0, 0).circle(2).size, 8)
    assertEquals(
      Vec(0, 0).circle(2).toSet,
      Set(Vec(-2, 0), Vec(0, -2), Vec(2, 0), Vec(0, 2), Vec(-1, -1), Vec(-1, 1), Vec(1, -1), Vec(1, 1))
    )
    assertEquals(
      Vec(3, 5).circle(2).toSet,
      Set(Vec(1, 5), Vec(3, 3), Vec(5, 5), Vec(3, 7), Vec(2, 4), Vec(2, 6), Vec(4, 4), Vec(4, 6))
    )
  }

  test("solution2 0") {
    assertEquals(solution2(parseInput(input0), 2, 0), 4)
    assertEquals(solution2(parseInput(input0), 2, 1), 1)
    assertEquals(solution2(parseInput(input0), 2, 2), 1)
    assertEquals(solution2(parseInput(input0), 2, 3), 0)
  }

  test("solution2") {
    assertEquals(solution2(parseInput(input1), 20, 50), 285)
//    assertEquals(solution2(parseInput(input1), 20, 52), 31)
//    assertEquals(solution2(parseInput(input1), 20, 54), 29)
//    assertEquals(solution2(parseInput(input1), 20, 56), 39)
//    assertEquals(solution2(parseInput(input1), 20, 58), 25)
//    assertEquals(solution2(parseInput(input1), 20, 60), 23)
//    assertEquals(solution2(parseInput(input1), 20, 62), 20+19+ 12+14+12+29)
    assertEquals(solution2(parseInput(input1), 20, 64), 86)
    assertEquals(solution2(parseInput(input1), 20, 66), 67)
    assertEquals(solution2(parseInput(input1), 20, 68), 55)
    assertEquals(solution2(parseInput(input1), 20, 70), 41)

    assertEquals(solution2(parseInput(input1), 20, 72), 29)
    assertEquals(solution2(parseInput(input1), 20, 74), 7)
    assertEquals(solution2(parseInput(input1), 20, 76), 3)
  }
}
