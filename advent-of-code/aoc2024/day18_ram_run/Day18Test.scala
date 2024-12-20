//> using target.scope test
import Day18.*
import scala.jdk.StreamConverters.*

class Day18Test extends munit.FunSuite {
  val input: List[String] =
    """one
      |two""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input), Input(List("one", "two")))
  }

  // part 1
  test("solution1"){
    assertEquals(solution1(parseInput(input)), 2)
  }

  // part 2
}
