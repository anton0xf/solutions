package unit5.lesson3
// https://stepik.org/lesson/106512/step/3?unit=81038

object PartialLog {
  val log: PartialFunction[Double, Double] = {
    case x if x > 0 => Math.log(x)
  }
}
