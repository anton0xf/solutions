//> using target.scope test
import Day18.*
import scala.jdk.StreamConverters.*

class Day18Test extends munit.FunSuite {
  val input: List[String] =
    """5,4
      |4,2
      |4,5
      |3,0
      |2,1
      |6,3
      |2,4
      |1,5
      |0,6
      |3,3
      |2,6
      |5,1
      |1,2
      |5,5
      |2,5
      |6,5
      |1,4
      |0,4
      |6,4
      |1,1
      |6,1
      |1,0
      |0,5
      |1,6
      |2,0""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput("5,4\n2,0".lines().toScala(List)), List(Vec(5, 4), Vec(2, 0)))
  }

  private val testMem: Mem = Mem(Vec(6, 6), parseInput(input).take(12).toSet)

  test("show") {
    assertEquals(
      testMem.show,
      """...#...
        |..#..#.
        |....#..
        |...#..#
        |..#..#.
        |.#..#..
        |#.#....""".stripMargin
    )
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(testMem), 22)
  }

  test("findPath") {
    val mem = Mem(Vec(1, 1), Set(Vec(0, 1)))
    assertEquals(findPath(mem), Some(List(Vec(0, 0), Vec(1, 0), Vec(1, 1))))
  }

  // part 2
}
