package part4

import scala.math.BigDecimal.int2bigDecimal

object Step_4_7_12 {
  def main(args: Array[String]): Unit = {
    val capacity = 100
    val power = 4
//    val powerOfTwo = Stream.fill(capacity)(2.toBigInt).scanLeft(2.toBigInt)(_ * _).take(power).#::(1).toList.last
    val powersOfTwo = Stream.continually(2.toBigInt).scanLeft(1.toBigInt)(_ * _)
    val powerOfTwo = powersOfTwo(power)
    println(powerOfTwo)
  }
}
