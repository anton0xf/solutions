//> using target.scope test
import Day07.*
import scala.jdk.StreamConverters.*

class Day07Test extends munit.FunSuite {
  // part 1
  val input: Input =
    """190: 10 19
      |3267: 81 40 27
      |83: 17 5
      |156: 15 6
      |7290: 6 8 6 15
      |161011: 16 10 13
      |192: 17 8 14
      |21037: 9 7 18 13
      |292: 11 6 16 20""".stripMargin.lines().toScala(List).map(parseEq)

  test("parseEq") {
    assertEquals(parseEq("190: 10 19"), Eq(BigInt(190), List(BigInt(10), BigInt(19))))
  }
  test("solveEq") {
    assertEquals(solveEq(Eq(BigInt(190), List(10, 19).map(BigInt.apply))), Some(BigInt(190)))
    assertEquals(solveEq(parseEq("3267: 81 40 27")), Some(BigInt(3267)))
    assertEquals(solveEq(parseEq("292: 11 6 16 20")), Some(BigInt(292)))
    assertEquals(solveEq(parseEq("83: 17 5")), None)
  }
  test("solution1") {
    assertEquals(solution1(input), BigInt(3749))
  }
}
