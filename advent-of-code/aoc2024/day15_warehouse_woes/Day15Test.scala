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
    assertEquals(data.p, Vec(3, 1))
    assertEquals(data.cmds, List(Vec(-1, 0), Vec(0, -1), Vec(-1, 0), Vec(1, 0)))
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input0)), 101)
    assertEquals(solution1(parseInput(input1)), 2028)
    assertEquals(solution1(parseInput(input2)), 10092)
  }

  // part 2
  val input3: List[String] =
    """#######
      |#...#.#
      |#.....#
      |#..OO@#
      |#..O..#
      |#.....#
      |#######
      |
      |<vv<<^^<<^^""".stripMargin.lines().toScala(List)

  test("toState2") {
    assertEquals(
      toState2(parseInput(input3)).show,
      """##############
        |##......##..##
        |##..........##
        |##....[][]@.##
        |##....[]....##
        |##..........##
        |##############""".stripMargin
    )
  }

  test("simulate2") {
    val init = toState2(parseInput(input3))
    assertEquals(
      simulate2(Nil, init).show,
      """##############
        |##......##..##
        |##..........##
        |##....[][]@.##
        |##....[]....##
        |##..........##
        |##############""".stripMargin
    )
    assertEquals(
      simulate2("<".map(dirs.apply).toList, init).show,
      """##############
        |##......##..##
        |##..........##
        |##...[][]@..##
        |##....[]....##
        |##..........##
        |##############""".stripMargin
    )
    assertEquals(
      simulate2("<v".map(dirs.apply).toList, init).show,
      """##############
        |##......##..##
        |##..........##
        |##...[][]...##
        |##....[].@..##
        |##..........##
        |##############""".stripMargin
    )
    assertEquals(
      simulate2("<vv<".map(dirs.apply).toList, init).show,
      """##############
        |##......##..##
        |##..........##
        |##...[][]...##
        |##....[]....##
        |##......@...##
        |##############""".stripMargin
    )
    assertEquals(
      simulate2("<vv<<".map(dirs.apply).toList, init).show,
      """##############
        |##......##..##
        |##..........##
        |##...[][]...##
        |##....[]....##
        |##.....@....##
        |##############""".stripMargin
    )
    assertEquals(
      simulate2("<vv<<^".map(dirs.apply).toList, init).show,
      """##############
        |##......##..##
        |##...[][]...##
        |##....[]....##
        |##.....@....##
        |##..........##
        |##############""".stripMargin
    )
    assertEquals(
      simulate2("<vv<<^^".map(dirs.apply).toList, init).show,
      """##############
        |##......##..##
        |##...[][]...##
        |##....[]....##
        |##.....@....##
        |##..........##
        |##############""".stripMargin
    )
  }

  test("step2") {
    val input =
      """##############
        |##......##..##
        |##..........##
        |##...[][]...##
        |##....[]....##
        |##.....@....##
        |##############""".stripMargin.lines().toScala(List)
    val state: State2 = parseMap2(input)
    assertEquals(
      step2(dirs('^'), state).show,
      """##############
        |##......##..##
        |##...[][]...##
        |##....[]....##
        |##.....@....##
        |##..........##
        |##############""".stripMargin
    )
  }

  test("findMovableCluster") {
    val input =
      """##############
        |##......##..##
        |##..........##
        |##...[][]...##
        |##....[]....##
        |##.....@....##
        |##############""".stripMargin.lines().toScala(List)
    val state: State2 = parseMap2(input)
    assertEquals(
      findMovableCluster(Vec(0, -1), Vec(7, 4), state.map),
      Some(List(
        Vec(5, 3) -> Obj2.BoxL, Vec(6, 3) -> Obj2.BoxR,
        Vec(7, 3) -> Obj2.BoxL, Vec(8, 3) -> Obj2.BoxR,
        Vec(6, 4) -> Obj2.BoxL, Vec(7, 4) -> Obj2.BoxR,
      ))
    )
  }

  test("solution2") {
    assertEquals(solution2(parseInput(input0)), 102)
    // assertEquals(solution2(parseInput(input1)), 2028)
    assertEquals(solution2(parseInput(input2)), 9021)
  }
}
