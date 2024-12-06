//> using target.scope test
import Day05.*
import scala.jdk.StreamConverters.*

class Day05Test extends munit.FunSuite {
  val input0 =
    """1|2
      |
      |1,3,2
      |3,2,1
      |""".stripMargin.lines().toScala(List)

  val input1 =
    """47|53
      |97|13
      |97|61
      |97|47
      |75|29
      |61|13
      |75|53
      |29|13
      |97|29
      |53|29
      |61|53
      |97|53
      |61|29
      |47|13
      |75|47
      |97|75
      |47|61
      |75|61
      |47|29
      |75|13
      |53|13
      |
      |75,47,61,53,29
      |97,61,53,29,13
      |75,29,13
      |75,97,47,61,53
      |61,13,29
      |97,13,75,29,47""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(
      parseInput(input0.iterator),
      Input(
        Set(Rule(1, 2)),
        List(Update(Vector(1, 3, 2)), Update(Vector(3, 2, 1)))
      )
    )
  }
  test("rightOrder") {
    val check = rightOrder(List(Rule(1, 2)))
    assertEquals(check(Update(Vector(1,2))), true)
    assertEquals(check(Update(Vector(1,3,2))), true)
    assertEquals(check(Update(Vector(1,3))), true)
    assertEquals(check(Update(Vector(3,2))), true)
    assertEquals(check(Update(Vector(2,1))), false)
    assertEquals(check(Update(Vector(2,3,1))), false)
  }
  test("getMid") {
    assertEquals(getMid(Vector(1)), 1)
    assertEquals(getMid(Vector(1,2,3)), 2)
    assertEquals(getMid(Vector(1,2,3,4,5)), 3)
  }
  test("solution1"){
    assertEquals(solution1(parseInput(input0.iterator)), 3)
    assertEquals(solution1(parseInput(input1.iterator)), 143)
  }
  test("solution2"){
    assertEquals(solution2(parseInput(input0.iterator)), 1)
    assertEquals(solution2(parseInput(input1.iterator)), 123)
  }
}
