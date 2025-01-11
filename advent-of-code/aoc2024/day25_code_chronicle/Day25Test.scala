//> using target.scope test
import Day25.*
import Day25.Schema.*
import scala.jdk.StreamConverters.*

class Day25Test extends munit.FunSuite {
  val input0: List[String] =
    """##
      |.#
      |..
      |
      |..
      |#.
      |##
      |""".stripMargin.lines().toScala(List)

  val input1: List[String] =
    """#####
      |.####
      |.####
      |.####
      |.#.#.
      |.#...
      |.....
      |
      |#####
      |##.##
      |.#.##
      |...##
      |...#.
      |...#.
      |.....
      |
      |.....
      |#....
      |#....
      |#...#
      |#.#.#
      |#.###
      |#####
      |
      |.....
      |.....
      |#.#..
      |###..
      |###.#
      |###.#
      |#####
      |
      |.....
      |.....
      |.....
      |#....
      |#.#..
      |#.#.#
      |#####""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input0), Input(1, List(Lock(List(0, 1)), Key(List(1, 0)))))

    val data1 = parseInput(input1)
    assertEquals(data1.maxPins, 5)
    assertEquals(data1.locks, List(Lock(List(0, 5, 3, 4, 3)), Lock(List(1, 2, 0, 5, 3))))
    assertEquals(data1.keys, List(Key(List(5, 0, 2, 1, 3)), Key(List(4, 3, 4, 0, 2)), Key(List(3, 0, 2, 0, 1))))
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input1)), 3)
  }

  test("matches") {
    assertEquals(matches(5)(Key(List(3,0,2,0,1)))(Lock(List(0,5,3,4,3))), true)
    assertEquals(matches(5)(Key(List(5,0,2,1,3)))(Lock(List(0,5,3,4,3))), false)
  }

  // part 2
}
