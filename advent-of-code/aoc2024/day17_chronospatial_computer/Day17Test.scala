//> using target.scope test
import Day17.*
import scala.jdk.StreamConverters.*

class Day17Test extends munit.FunSuite {
  test("parseRegister") {
    assertEquals(parseRegister('A', "Register A: 729"), 729)
  }

  test("parseProgram") {
    assertEquals(parseProgram("Program: 0,1,5,4,3,0"), Vector(0, 1, 5, 4, 3, 0))
  }

  val input: List[String] =
    """Register A: 729
      |Register B: 0
      |Register C: 0
      |
      |Program: 0,1,5,4,3,0""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input), Computer(Vector(0, 1, 5, 4, 3, 0), 729, 0, 0))
  }

  // part 1

  test("exec 1") {
    // If register C contains 9, the program 2,6 would set register B to 1.
    val c = Computer(Vector(2,6), 0, 0, 9).exec
    assertEquals(c.b, 1)
  }
  test("exec 2") {
    // If register A contains 10, the program 5,0,5,1,5,4 would output 0,1,2.
    val c = Computer(Vector(5,0,5,1,5,4), 10, 0, 0).exec
    assertEquals(c.out, Vector(0,1,2))
  }
  test("exec 3") {
    // If register A contains 2024, the program 0,1,5,4,3,0 would output 4,2,5,6,7,7,7,7,3,1,0 and leave 0 in register A.
    val c = Computer(Vector(0,1,5,4,3,0), 2024, 0, 0).exec
    assertEquals(c.a, 0)
    assertEquals(c.out, Vector(4,2,5,6,7,7,7,7,3,1,0))
  }
  test("exec 4") {
    // If register B contains 29, the program 1,7 would set register B to 26.
    val c = Computer(Vector(1,7), 0, 29, 0).exec
    assertEquals(c.b, 26)
  }
  test("exec 5") {
    // If register B contains 2024 and register C contains 43690, the program 4,0 would set register B to 44354.
    val c = Computer(Vector(4,0), 0, 2024, 43690).exec
    assertEquals(c.b, 44354)
  }
  test("exec(input)") {
    val c = parseInput(input).exec
    assertEquals(c.out, Vector(4,6,3,5,6,3,5,2,1,0))
  }

  test("solution1") {
    assertEquals(solution1(parseInput(input)), "4,6,3,5,6,3,5,2,1,0")
  }

  // part 2
  val input2: List[String] =
    """Register A: 2024
      |Register B: 0
      |Register C: 0
      |
      |Program: 0,3,5,4,3,0""".stripMargin.lines().toScala(List)

  test("solution2") {
    assertEquals(solution2(parseInput(input2)), 117440)
  }

  test("exec2") {
    val init = parseInput(input2).copy(a = 117440)
    val res = exec2(init)
    println(res.get.show)
    assertEquals(res.get.out, init.program)
  }
}
