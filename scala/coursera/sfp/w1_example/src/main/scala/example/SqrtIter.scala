package example

import scala.annotation.tailrec
import scala.math.abs

object SqrtIter {
  def improve(guess: Double, x: Double): Double = (guess + x / guess) / 2
  def isGoodEnough(guess: Double, x: Double): Boolean = abs(guess*guess - x) < 0.001
  def sqrt(x: Double): Double =
    @tailrec
    def go(guess: Double): Double = if isGoodEnough(guess, x) then guess else go(improve(guess, x))
    go(1.0)
}
