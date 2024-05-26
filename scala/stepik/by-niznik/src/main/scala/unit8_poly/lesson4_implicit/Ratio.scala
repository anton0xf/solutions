package unit8_poly.lesson4_implicit
// https://stepik.org/lesson/106535/step/3?unit=81061

final case class Ratio private(num: BigInt, den: BigInt)

object Ratio {
  def apply(num: BigInt, den: BigInt): Ratio = {
    val d = num.gcd(den) * (if(den < 0) -1 else 1)
    new Ratio(num / d, den / d)
  }

  implicit class RatioOps[T](val num: T) {
    def \\(den: BigInt)(implicit toBigInt: T => BigInt): Ratio = Ratio(num, den)
  }

  implicit val ordering: Ordering[Ratio] = (x: Ratio, y: Ratio) => (x.num * y.den).compare(x.den * y.num)
}
