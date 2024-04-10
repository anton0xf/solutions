package unit3.lesson2
// step 4: https://stepik.org/lesson/106498/step/4

import scala.io.StdIn

object Crisps {
  import scala.math.BigDecimal.RoundingMode.HALF_UP
  def crispsWeight(
      weight: BigDecimal,
      potatoWaterRatio: Double,
      crispsWaterRatio: Double
  ): BigDecimal = {
    val res = weight / (1 - crispsWaterRatio) * (1 - potatoWaterRatio)
    res.setScale(5, HALF_UP)
  }

  def main(args: Array[String]): Unit = {
    print("Enter 3 numbers: ")
    val weight = StdIn.readDouble()
    val potatoRat = StdIn.readDouble()
    val crispsRat = StdIn.readDouble()
    val res = crispsWeight(weight, potatoRat, crispsRat)
    println("Crisps weight: " + res)
  }
}
