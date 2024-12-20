import scala.collection.immutable
import scala.util.Using
import scala.io.Source
import scala.annotation.tailrec

object Day11 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day11_plutonian_pebbles/input")) { source =>
      val input = parseInput(source.getLines().next())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  type Input = List[BigInt]

  def parseInput(line: String): Input = line.split(' ').map(BigInt.apply).toList

  // part 1
  def solution1(input: Input): Int = {
    blinks(input)(25).size
  }

  def blinks(ns: Input): LazyList[Input] = LazyList.iterate(ns)(blink)

  def blink(ns: Input): Input = {
    @tailrec
    def go(ns: List[BigInt], acc: List[BigInt]): List[BigInt] = ns match {
      case Nil => acc
      case n :: ns =>
        if n == BigInt(0)
        then go(ns, BigInt(1) :: acc)
        else if evenDigits(n) then go(ns, splitDigits(n).reverse ++ acc)
        else go(ns, n * 2024 :: acc)
    }
    go(ns, Nil).reverse
  }

  def evenDigits(n: BigInt): Boolean = n.toString().size % 2 == 0

  def splitDigits(n: BigInt): List[BigInt] = {
    val s = n.toString()
    List(s.substring(0, s.length() / 2), s.substring(s.length() / 2))
      .map(BigInt.apply)
  }

  // part 2
  def solution2(input: Input): BigInt = {
    solution(input, 75)
  }

  def solution(ns: List[BigInt], blinks: Int): BigInt = {
    var cache: scala.collection.mutable.Map[(BigInt, Int), BigInt] = scala.collection.mutable.Map()
    def go(n: BigInt, blinks: Int): BigInt = 
      if blinks == 0 then BigInt(1)
      else cache.getOrElseUpdate((n, blinks), {
        if n == BigInt(0) then go(BigInt(1), blinks - 1)
        else if evenDigits(n) then splitDigits(n).map(go(_, blinks - 1)).sum
        else go(n * 2024, blinks - 1)
      })
    val res = ns.iterator.map(go(_, blinks)).sum
    // println(s"cache size: ${cache.size}")
    res
  }  
}
