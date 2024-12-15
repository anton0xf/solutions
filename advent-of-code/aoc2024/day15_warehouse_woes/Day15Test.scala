//> using target.scope test
import Day15.*
import scala.jdk.StreamConverters.*

class Day15Test extends munit.FunSuite {
  val input0: List[String] =
    """######
      |#.O@.#
      |######
      |
      |<^<>""".stripMargin.lines().toScala(List)

  val input1: List[String] =
    """########
      |#..O.O.#
      |##@.O..#
      |#...O..#
      |#.#.O..#
      |#...O..#
      |#......#
      |########
      |
      |<^^>>>vv<v>>v<<""".stripMargin.lines().toScala(List)

  val input2: List[String] =
    """##########
      |#..O..O.O#
      |#......O.#
      |#.OO..O.O#
      |#..O@..O.#
      |#O#..O...#
      |#O..O..O.#
      |#.OO.O.OO#
      |#....O...#
      |##########
      |
      |<vv>^<v^>v>^vv^v>v<>v^v<v<^vv<<<^><<><>>v<vvv<>^v^>^<<<><<v<<<v^vv^v>^
      |vvv<<^>^v^^><<>>><>^<<><^vv^^<>vvv<>><^^v>^>vv<>v<<<<v<^v>^<^^>>>^<v<v
      |><>vv>v^v^<>><>>>><^^>vv>v<^^^>>v^v^<^^>v^^>v^<^v>v<>>v^v^<v>v^^<^^vv<
      |<<v<^>>^^^^>>>v^<>vvv^><v<<<>^^^vv^<vvv>^>v<^^^^v<>^>vvvv><>>v^<<^^^^^
      |^><^><>>><>^^<<^^v>>><^<v>^<vv>>v>>>^v><>^v><<<<v>>v<v<v>vvv>^<><<>^><
      |^>><>^v<><^vvv<^^<><v<<<<<><^v<<<><<<^^<v<^^^><^>>^<v^><<<^>>^v<v^v<v^
      |>^>>^v>vv>^<<^v<>><<><<v<<v><>v<^vv<<<>^^v^>^^>>><<^v>>v^v><^^>>^<>vv^
      |<><^^>^^^<><vvvvv^v<v<<>^v<v>v<<^><<><<><<<^^<<<^<<>><<><^^^>^^<>^>v<>
      |^^>vv<^v^v<vv>^<><v<^v>^^^>>>^^vvv^>vvv<>>>^<^>>>>>^<<^v>^vvv<>^<><<v>
      |v^^>>><<^^<>>^v^<v^vv<>v^<<>^<^v^v><^<<<><<^<v><v<>vv>>v><v^<vv<>v^<<^""".stripMargin
      .lines()
      .toScala(List)

  test("parseInput") {
    val data = parseInput(input0)
    assertEquals(data.map.toList.filter((_, x) => x == Obj.Box).map((p, _) => p), List(Vec(2, 1)))
    assertEquals(data.p, Vec(3,1))
    assertEquals(data.cmds, List(Vec(-1, 0), Vec(0, -1), Vec(-1, 0), Vec(1, 0)))
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input0)), 101)
    assertEquals(solution1(parseInput(input1)), 2028)
    assertEquals(solution1(parseInput(input2)), 10092)
  }

  // part 2
}
