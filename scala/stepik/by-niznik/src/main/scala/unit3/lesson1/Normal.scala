package unit3.lesson1
// step 5: https://stepik.org/lesson/106537/step/5?unit=81063

object Normal extends App {
  def normalDistribution(mu: Double, sigma: Double, x: Double): Double = {
    import scala.math._
    val d = x - mu
    exp(- d * d / (2 * sigma * sigma)) / (sigma * sqrt(2 * Pi))
  }
  println("p(0, 1)(1) = " + normalDistribution(0, 1, 1))
}
