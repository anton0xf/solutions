//> using target.scope test
import Day13.*
import InputParser.*

import java.io.StringReader
import scala.jdk.StreamConverters.*

class Day13Test extends munit.FunSuite {
  val buttonA1 = "Button A: X+94, Y+34"
  val buttonB1 = "Button B: X+22, Y+67"
  val prize1 = "Prize: X=8400, Y=5400"

  val machine1: String = List(buttonA1, buttonB1, prize1).mkString("\n")

  val input: String =
    """Button A: X+94, Y+34
      |Button B: X+22, Y+67
      |Prize: X=8400, Y=5400
      |
      |Button A: X+26, Y+66
      |Button B: X+67, Y+21
      |Prize: X=12748, Y=12176
      |
      |Button A: X+17, Y+86
      |Button B: X+84, Y+37
      |Prize: X=7870, Y=6450
      |
      |Button A: X+69, Y+23
      |Button B: X+27, Y+71
      |Prize: X=18641, Y=10279""".stripMargin

  test("parse button") {
    assertEquals(parse(button('A'), buttonA1).get, Vec(94, 34))
    assertEquals(parse(button('B'), buttonB1).get, Vec(22, 67))
  }

  test("parse prize") {
    assertEquals(parse(prize, prize1).get, Vec(8400, 5400))
  }

  test("parse machine") {
    assertEquals(
      parse(machine, machine1).get,
      Machine(a = Vec(94, 34), b = Vec(22, 67), prize = Vec(8400, 5400))
    )
  }

  test("parseInput") {
    assertEquals(
      parseData(StringReader(input)),
      Data(
        List(
          Machine(a = Vec(94, 34), b = Vec(22, 67), prize = Vec(8400, 5400)),
          Machine(a = Vec(26, 66), b = Vec(67, 21), prize = Vec(12748, 12176)),
          Machine(a = Vec(17, 86), b = Vec(84, 37), prize = Vec(7870, 6450)),
          Machine(a = Vec(69, 23), b = Vec(27, 71), prize = Vec(18641, 10279))
        )
      )
    )
  }

  // part 1
  test("solve"){
    assertEquals(solve(Machine(a = Vec(94, 34), b = Vec(22, 67), prize = Vec(8400, 5400))), Some(Vec(80, 40)))
    assertEquals(solve(Machine(a = Vec(26, 66), b = Vec(67, 21), prize = Vec(12748, 12176))), None)
    assertEquals(solve(Machine(a = Vec(17, 86), b = Vec(84, 37), prize = Vec(7870, 6450))), Some(Vec(38,86)))
    assertEquals(solve(Machine(a = Vec(69, 23), b = Vec(27, 71), prize = Vec(18641, 10279))), None)
  }

  test("solution1") {
    assertEquals(solution1(parseData(StringReader(input))), 480)
  }

  // part 2
}
