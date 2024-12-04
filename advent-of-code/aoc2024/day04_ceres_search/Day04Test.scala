//> using target.scope test
import Day04.*
import scala.jdk.StreamConverters.*

class Day04Test extends munit.FunSuite {
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
}
