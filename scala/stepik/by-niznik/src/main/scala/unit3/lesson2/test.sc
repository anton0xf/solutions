// step 2: https://stepik.org/lesson/106498/step/2
val d: Float = 1.1F

import scala.math.pow
val x = pow(2, 3)

val y = {
  import scala.math.BigInt.int2bigInt
  2 pow 3
}

val z = {
  import scala.math.BigDecimal.int2bigDecimal
  2 pow 3
}

import scala.collection.Seq
case class MyInt(i: Int) {
  def pow(j: MyInt): MyInt = MyInt(Seq.fill(j.i)(i).product)
}
//val w = MyInt(2).pow(MyInt(3))
val w = MyInt(2) pow MyInt(3)

// step 3: https://stepik.org/lesson/106498/step/3
val s = (1: Short)

val pileOfPooStr = "\uD83D\uDCA9"
val pileOfPooSymbol = Symbol(pileOfPooStr)
val someSymbol = Symbol("anton0xf")
//val pileOfPooChar = '💩'
// error: illegal codepoint in Char constant: '\ud83d\udca9'

('A'.toInt + 10).toChar
'K' - 'A'

for(i <- 1 to 10) yield { i * 2 }