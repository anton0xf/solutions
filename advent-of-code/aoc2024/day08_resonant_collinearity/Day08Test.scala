//> using target.scope test
import Day08.*
import scala.jdk.StreamConverters.*

class Day08Test extends munit.FunSuite {
  // part 1
  val input: List[String] =
    """............
      |........0...
      |.....0......
      |.......0....
      |....0.......
      |......A.....
      |............
      |............
      |........A...
      |.........A..
      |............
      |............""".stripMargin.lines().toScala(List)

  test("parseEq") {
    assertEquals(
      parseInput(input.iterator),
      Input(
        size = (12, 12),
        map = Map(
          Pos(1, 8) -> '0',
          Pos(2, 5) -> '0',
          Pos(3, 7) -> '0',
          Pos(4, 4) -> '0',
          Pos(5, 6) -> 'A',
          Pos(8, 8) -> 'A',
          Pos(9, 9) -> 'A'
        )
      )
    )
  }

  test("solution1"){
    assertEquals(solution1(parseInput(input.iterator)), 14)
  }

}
