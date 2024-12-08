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
  // part 2
  test("solveEq2") {
    assertEquals(solveEq2(parseEq("156: 15 6")), Some(BigInt(156)))
    assertEquals(solveEq2(parseEq("45: 1 3 5")), Some(BigInt(45)))
    assertEquals(solveEq2(parseEq("7290: 6 8 6 15")), Some(BigInt(7290)))
    assertEquals(solveEq2(parseEq("192: 17 8 14")), Some(BigInt(192)))
    assertEquals(solveEq2(Eq(BigInt("18021496390543"), List(5, 90, 53, 6, 1, 40, 976, 36, 4))), None)
    assertEquals(solveEq2(parseEq("15: 15")), Some(BigInt(15)))
    assertEquals(solveEq2(parseEq("15: 0 15")), Some(BigInt(15)))
    assertEquals(solveEq2(parseEq("15: 2 15")), None)
    assertEquals(solveEq2(parseEq("618: 3 100 456 57 5")), None)
  }
  test("solveEq2'") {
    assertEquals(solveEq2(parseEq("618: 3 100 456 57 5")), None)
  }
  test("solution2") {
    assertEquals(solution2(input), BigInt(11387))
  }
}
