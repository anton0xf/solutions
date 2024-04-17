package unit5.lesson1
// step 5: https://stepik.org/lesson/106539/step/5?unit=81065
// https://en.wikipedia.org/wiki/Coprime_integers

import scala.io.StdIn

object Coprime {
  def main(args: Array[String]): Unit = {
    val n = StdIn.readInt()
    val pairs = getCoprimes(n)
    for ((i, j) <- pairs) println(s"$i $j")
  }

  def getCoprimes(n: Int): Seq[(Int, Int)] = {
    for {
      i <- 1 until n
      j <- 1 until n
      if BigInt(i).gcd(BigInt(j)) == 1
    } yield (i, j)
  }
}
