//> using target.scope test
import Day04.*
import scala.jdk.StreamConverters.*

class Day04Test extends munit.FunSuite {
  // part 1
  val input: Input =
    """..X...
    |.SAMX.
    |.A..A.
    |XMAS.S
    |.X....
    |""".stripMargin.lines().toScala(Vector).map(_.toVector)

  test("dirs") {
    assertEquals(dirs.size, 8)
    println(dirs)
    assertEquals(
      dirs,
      List((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1))
    )
  }

  test("findWord") {
    assertEquals(findWord(input, (0, 2), (1, 1)), true)
    assertEquals(findWord(input, (0, 2), (1, 0)), false)
    assertEquals(findWord(input, (0, 2), (-1, 0)), false)
  }
  test("solution1") {
    assertEquals(solution1(input), 4)
  }

  // part 2
  val input2s: Input =
    """M.S
      |.A.
      |M.S""".stripMargin.lines().toScala(Vector).map(_.toVector)

  val input2: Input =
    """.M.S......
      |..A..MSMS.
      |.M.S.MAA..
      |..A.ASMSM.
      |.M.S.M....
      |..........
      |S.S.S.S.S.
      |.A.A.A.A..
      |M.M.M.M.M.
      |..........""".stripMargin.lines().toScala(Vector).map(_.toVector)

    test("solution2") {
      assertEquals(solution2(input2s), 1)
      assertEquals(solution2(input2), 9)
    }

    test("checkPattern") {
      assertEquals(checkPattern(input2s, (1, 1)))
    }
}
