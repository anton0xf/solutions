//> using target.scope test
import Day00.*
import scala.jdk.StreamConverters.*

class Day00Test extends munit.FunSuite {
  val input: List[String] =
    """one
      |two""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input.iterator), Input(List("one", "two")))
  }

  // part 1
  test("solution1"){
    assertEquals(solution1(parseInput(input.iterator)), 2)
  }

  // part 2
}
