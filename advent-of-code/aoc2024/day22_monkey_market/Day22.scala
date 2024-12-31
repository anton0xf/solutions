import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day22 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day22_monkey_market/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"input size: ${input.size}")
      println(s"part 1: ${solution1(input)}")
    }
  }

  type Input = List[BigInt]

  def parseInput(lines: IterableOnce[String]): Input = lines.iterator.map(BigInt.apply).toList

  // part 1
  def solution1(input: Input): BigInt = {
    input.map(simulate).sum
  }

  def simulate(s: BigInt): BigInt = LazyList.iterate(s)(next).drop(2000).head

  def next(s: BigInt): BigInt = {
    val s1 = prune(mix(s * 64, s))
    val s2 = prune(mix(s1 / 32, s1))
    prune(mix(s2 * 2048, s2))
  }

  def mix(n: BigInt, s: BigInt): BigInt = n ^ s
  def prune(n: BigInt): BigInt = n % BigInt("16777216")

  // part 2
}
