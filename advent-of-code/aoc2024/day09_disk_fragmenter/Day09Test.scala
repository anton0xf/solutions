//> using target.scope test
import Day09.*
import scala.jdk.StreamConverters.*

class Day09Test extends munit.FunSuite {
  val input: Input = "2333133121414131402"

  // part 1
  test("solution1"){
    assertEquals(solution1(input), BigInt(1928))
  }

  test("toBlocks") {
    assertEquals(showBlocks(toBlocks(input)), "00...111...2...333.44.5555.6666.777.888899")
  }

  test("defragment") {
    assertEquals(showBlocks(compact(toBlocks(input))), "0099811188827773336446555566..............")
  }

  // part 2
}
