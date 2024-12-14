//> using target.scope test
import Day14.*
import scala.jdk.StreamConverters.*

class Day14Test extends munit.FunSuite {
  val robot: String = "p=0,4 v=3,-3"
  val input: List[String] =
    """p=0,4 v=3,-3
      |p=6,3 v=-1,-3
      |p=10,3 v=-1,2
      |p=2,0 v=2,-1
      |p=0,0 v=1,3
      |p=3,0 v=-2,-2
      |p=7,6 v=-1,-3
      |p=3,0 v=-1,-2
      |p=9,3 v=2,3
      |p=7,3 v=-1,2
      |p=2,4 v=2,-3
      |p=9,5 v=-3,-3""".stripMargin.lines().toScala(List)

  val size: Vec = Vec(11, 7)

  test("parseRobot") {
    assertEquals(parseRobot(robot), Robot(Vec(0,4), Vec(3,-3)))
  }

  // part 1
  test("solution1"){
    assertEquals(solution1(parseInput(input), size), 12)
  }

  // part 2
}
