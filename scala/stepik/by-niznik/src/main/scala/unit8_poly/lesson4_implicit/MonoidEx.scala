package unit8_poly.lesson4_implicit
// https://stepik.org/lesson/106535/step/2?unit=81061

object MonoidEx {
  private def reduceMonoid[A](xs: List[A])(monoid: Monoid[A]) = xs.foldLeft(monoid.zero)(monoid.+)
  def concatAll(xs: List[String]): String = reduceMonoid(xs)(StringMonoid)
  def sumAll(xs: List[Int]): Int = reduceMonoid(xs)(IntMonoid)
  def forAll(xs: List[Boolean]): Boolean = reduceMonoid(xs)(BoolMonoid)
}

trait Monoid[A] {
  def zero: A
  def +(x: A, y: A): A
}

object StringMonoid extends Monoid[String] {
  override def zero: String = ""
  override def +(x: String, y: String): String = x + y
}

object IntMonoid extends Monoid[Int] {
  override def zero: Int = 0
  override def +(x: Int, y: Int): Int = x + y
}

object BoolMonoid extends Monoid[Boolean] {
  override def zero: Boolean = true
  override def +(x: Boolean, y: Boolean): Boolean = x && y
}



