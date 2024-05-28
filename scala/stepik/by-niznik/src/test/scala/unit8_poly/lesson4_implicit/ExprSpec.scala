package unit8_poly.lesson4_implicit

import munit.FunSuite
import ExprSyntax._
import unit8_poly.lesson4_implicit.Expr.Calc

class ExprSpec extends FunSuite {
  test("X to string") {
    def x[T: Expr]: T = X
    assertEquals(x, "X")
  }

  test("1 to string") {
    def one[T: Expr]: T = 1.lit
    assertEquals(one, "1")
  }

  test("(X+1) to string") {
    def xPlusOne[T: Expr]: T = X + 1.lit
    assertEquals(xPlusOne, "(X)+(1)")
  }

  test("simple expression to string") {
    def f[T: Expr]: T = -X - 2.lit + Y
    assertEquals(f, "((-(X))-(2))+(Y)")
  }

  test("complex expression to string") {
    def f[T: Expr]: T = X * X + 2.lit * (Y + Z * X * 2.lit) - 7.lit * Z + 4.lit
    assertEquals(f, "((((X)*(X))+((2)*((Y)+(((Z)*(X))*(2)))))-((7)*(Z)))+(4)")
  }

  test("calc X") {
    def x[T: Expr]: T = X
    assertEquals(x[Calc[Double]].apply(Map("x" -> 2)), 2.0)
  }

  test("calc 1") {
    def one[T: Expr]: T = 1.lit
    assertEquals(one[Calc[Double]].apply(Map("x" -> 2)), 1.0)
  }

  test("calc (X+1)") {
    def xPlusOne[T: Expr]: T = X + 1.lit
    assertEquals(xPlusOne[Calc[Double]].apply(Map("x" -> 2)), 3.0)
  }

  test("complex expression to string") {
    def f[T: Expr]: T = X * X + 2.lit * (Y + Z * X * 2.lit) - 7.lit * Z + 4.lit
    assertEquals(f[Calc[Double]].apply(Map("x" -> 1, "y" -> -1, "z" -> 0.2)), 2.4)
  }

}
