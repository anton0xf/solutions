//> using target.scope test
import Day22.*
import scala.jdk.StreamConverters.*

class Day22Test extends munit.FunSuite {
  val input: List[String] =
    """1
      |10
      |100
      |2024""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input), List(1, 10, 100, 2024).map(BigInt.apply))
  }

  // part 1
  test("solution1") {
    assertEquals(solution1(parseInput(input)), BigInt("37327623"))
  }

  test("simulate") {
    assertEquals(simulate(BigInt(1)), BigInt("8685429"))
    assertEquals(simulate(BigInt(10)), BigInt("4700978"))
    assertEquals(simulate(BigInt(100)), BigInt("15273692"))
    assertEquals(simulate(BigInt(2024)), BigInt("8667524"))
  }

  test("next") {
    assertEquals(next(BigInt(123)), BigInt(15887950))
    assertEquals(
      LazyList.iterate(BigInt(123))(next).tail.take(10).toList,
      List(15887950, 16495136, 527345, 704524, 1553684, 12683156, 11100544, 12249484, 7753432, 5908254)
        .map(BigInt.apply)
    )
  }

  test("mix") {
    assertEquals(mix(BigInt(15), BigInt(42)), BigInt(37))
  }

  test("prune") {
    assertEquals(prune(BigInt("100000000")), BigInt("16113920"))
  }

  // part 2
  test("solution2") {
    assertEquals(solution2(List(1, 2, 3, 2024).map(BigInt.apply)), 23)
  }

  test("seqMap") {
    assertEquals(seqMap(9)(BigInt(123)), Map[Vector[Byte], Byte](
      Vector[Byte](-3, 6, -1, -1) -> 4,
      Vector[Byte](6, -1, -1, 0) -> 4,
      Vector[Byte](-1, -1, 0, 2) -> 6,
      Vector[Byte](-1, 0, 2, -2) -> 4,
      Vector[Byte](0, 2, -2, 0) -> 4,
      Vector[Byte](2, -2, 0, -2) -> 2,
    ))
  }
}
