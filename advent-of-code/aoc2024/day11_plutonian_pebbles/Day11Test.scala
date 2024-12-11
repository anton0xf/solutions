//> using target.scope test
import Day11.*

class Day11Test extends munit.FunSuite {
  val input0: String = "0 1 10 99 999"
  val input1: String = "125 17"

  test("parseInput") {
    assertEquals(parseInput(input0), List(0, 1, 10, 99, 999).map(BigInt.apply))
    assertEquals(parseInput(input1), List(125, 17).map(BigInt.apply))
  }

  test("blink") {
    assertEquals(blink(parseInput(input0)), parseInput("1 2024 1 0 9 9 2021976"))
    assertEquals(blink(parseInput(input1)), parseInput("253000 1 7"))
  }

  test("blinks") {
    assertEquals(
      blinks(parseInput(input1)).take(7),
      LazyList(
        input1,
        "253000 1 7",
        "253 0 2024 14168",
        "512072 1 20 24 28676032",
        "512 72 2024 2 0 2 4 2867 6032",
        "1036288 7 2 20 24 4048 1 4048 8096 28 67 60 32",
        "2097446912 14168 4048 2 0 2 4 40 48 2024 40 48 80 96 2 8 6 7 6 0 3 2"
      ).map(parseInput)
    )
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input1)), 55312)
  }

  // part 2
  test("solution") {
    assertEquals(solution(parseInput(input1), 6), BigInt(22))
    assertEquals(solution(parseInput(input1), 25), BigInt(55312))
  }
}
