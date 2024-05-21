package unit8_poly.lesson4_implicit
// https://stepik.org/lesson/106535/step/2?unit=81061

trait Monoid[A] {
  def zero: A
  def +(x: A, y: A): A
}

object Monoid {
  implicit val stringMonoid: Monoid[String] = new Monoid[String] {
    override def zero: String = ""
    override def +(x: String, y: String): String = x + y
  }

  implicit object IntMonoid extends Monoid[Int] {
    override def zero: Int = 0
    override def +(x: Int, y: Int): Int = x + y
  }

  implicit object BoolMonoid extends Monoid[Boolean] {
    override def zero: Boolean = true
    override def +(x: Boolean, y: Boolean): Boolean = x && y
  }
}

object MonoidEx {
  private def reduceMonoid[A](xs: List[A])(implicit monoid: Monoid[A]): A = xs.foldLeft(monoid.zero)(monoid.+)
  def concatAll(xs: List[String]): String = reduceMonoid(xs)
  def sumAll(xs: List[Int]): Int = reduceMonoid(xs)
  def forAll(xs: List[Boolean]): Boolean = reduceMonoid(xs)
}
