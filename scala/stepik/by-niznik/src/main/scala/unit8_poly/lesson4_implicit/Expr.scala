package unit8_poly.lesson4_implicit
// https://stepik.org/lesson/106535/step/5?unit=81061

trait Expr[T] {
  def literalInt(value: Int): T
  def variable(name: String): T
  def times(x: T, y: T): T
  def plus(x: T, y: T): T
  def minus(x: T, y: T): T = plus(x, negate(y))
  def negate(x: T): T = times(x, literalInt(-1))
}

object ExprSyntax {
  // def literalInt[T](value: Int)(implicit expr: Expr[T]): T = expr.literalInt(value)
  def X[T](implicit expr: Expr[T]): T = expr.variable("x")
  def Y[T](implicit expr: Expr[T]): T = expr.variable("y")
  def Z[T](implicit expr: Expr[T]): T = expr.variable("z")

  implicit class IntToExpr[T](x: Int)(implicit expr: Expr[T]) {
    def lit: T = expr.literalInt(x)
  }

  implicit class NumOps[T](val x: T) extends AnyVal {
    def +(y: T)(implicit expr: Expr[T]): T = expr.plus(x, y)
    def -(y: T)(implicit expr: Expr[T]): T = expr.minus(x, y)
    def *(y: T)(implicit expr: Expr[T]): T = expr.times(x, y)
    def unary_-(implicit expr: Expr[T]): T = expr.negate(x)
  }
}

object Expr {
  implicit val stringExpr: Expr[String] = new Expr[String] {
    override def literalInt(value: Int): String = s"$value"
    override def variable(name: String): String = s"${name.toUpperCase}"
    override def times(x: String, y: String): String = s"($x)*($y)"
    override def plus(x: String, y: String): String = s"($x)+($y)"
    override def minus(x: String, y: String): String = s"($x)-($y)"
    override def negate(x: String): String = s"-($x)"
  }

  type Calc[T] = Map[String, T] => T

  implicit def numericExpr[T](implicit numeric: Numeric[T]): Expr[Calc[T]] = new Expr[Calc[T]] {
    import Numeric.Implicits._
    override def literalInt(value: Int): Calc[T] = _ => numeric.fromInt(value)
    override def variable(name: String): Calc[T] = _(name)
    override def plus(x: Calc[T], y: Calc[T]): Calc[T] = vals => x(vals) + y(vals)
    override def times(x: Calc[T], y: Calc[T]): Calc[T] = vals => x(vals) * y(vals)
  }

  final case class Print(s: String, priority: Int, isLit: Boolean = false) {
    def print(outer: Int = 0): String = if (outer <= priority) s else s"($s)"
  }

  implicit val stringOrderExpr: Expr[Print] = new Expr[Print] {
    override def literalInt(value: Int): Print = Print(s"$value", 4, isLit = true)
    override def variable(name: String): Print = Print(s"${name.toUpperCase}", 5)
    override def times(x: Print, y: Print): Print =
      if (x.isLit && !y.isLit) Print(s"${x.print(3)}${y.print(3)}", 3)
      else Print(s"${x.print(3)}*${y.print(3)}", 3)
    override def plus(x: Print, y: Print): Print = Print(s"${x.print(2)}+${y.print(2)}", 2)
    override def minus(x: Print, y: Print): Print = Print(s"${x.print(2)}-${y.print(2)}", 2)
    override def negate(x: Print): Print = Print(s"-${x.print(1)}", 1)
  }
}
