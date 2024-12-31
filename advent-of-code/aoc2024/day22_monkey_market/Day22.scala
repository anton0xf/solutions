import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day22 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day22_monkey_market/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"input size: ${input.size}")
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
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
  def solution2(input: Input): Int = {
    val sum = input.iterator.map(seqMap(2000)).foldLeft(Map[Vector[Byte], Int]()) { (sum, m) =>
      m.foldLeft(sum) { (sum, seq2price) =>
        sum.updatedWith(seq2price._1) {
          case None    => Some(seq2price._2.toInt)
          case Some(n) => Some(n + seq2price._2.toInt)
        }
      }
    }
    sum.values.max
  }

  /** simulates m prices from initial secret number `s` and
   * returns Map from 4-values changes sequences to its first occurrence prices */
  def seqMap(m: Int)(s: BigInt): Map[Vector[Byte], Byte] = {
    val prices = LazyList.iterate(s)(next).map{n => (n % 10).toByte}.take(m + 1)
    val changes = (prices.tail zip prices).map(_ - _).map(_.toByte)
    val price2seq = prices.drop(4) zip changes.sliding(4).map(_.toVector)
    price2seq.foldLeft(Map[Vector[Byte], Byte]()){(map, p2s) =>
      map.updatedWith(p2s._2) {
        case None => Some(p2s._1)
        case x => x
      }
    }
  }
}
