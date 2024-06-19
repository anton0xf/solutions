package unit8_poly.lesson4_implicit

import munit.FunSuite
import ExprSyntax._
import unit8_poly.lesson4_implicit.Expr.{Calc, Print}

class ExprSpec extends FunSuite {
  test("X to string") {
    def x[T: Expr]: T = X
    assertEquals(x[String], "X")
  }

  test("1 to string") {
    def one[T: Expr]: T = 1.lit
    assertEquals(one[String], "1")
  }

  test("(X+1) to string") {
    def xPlusOne[T: Expr]: T = X + 1.lit
    assertEquals(xPlusOne[String], "(X)+(1)")
  }

  test("simple expression to string") {
    def f[T: Expr]: T = -X - 2.lit + Y
    assertEquals(f[String], "((-(X))-(2))+(Y)")
  }

  test("complex expression to string") {
    def f[T: Expr]: T = X * X + 2.lit * (Y + Z * X * 2.lit) - 7.lit * Z + 4.lit
    assertEquals(f[String], "((((X)*(X))+((2)*((Y)+(((Z)*(X))*(2)))))-((7)*(Z)))+(4)")
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

  test("X to string with priority") {
    def x[T: Expr]: T = X
    assertEquals(x[Print].print(), "X")
  }

  test("1 to string with priority") {
    def one[T: Expr]: T = 1.lit
    assertEquals(one[Print].print(), "1")
  }

  test("(X+1) to string with priority") {
    def xPlusOne[T: Expr]: T = X + 1.lit
    assertEquals(xPlusOne[Print].print(), "X+1")
  }

  test("(2*X) to string with priority") {
    def twoX[T: Expr]: T = 2.lit * X
    assertEquals(twoX[Print].print(), "2X")
  }

  test("(X*2) to string with priority") {
    def xTwo[T: Expr]: T = X * 2.lit
    assertEquals(xTwo[Print].print(), "X*2")
  }

  test("(X*Y) to string with priority") {
    def xy[T: Expr]: T = X * Y
    assertEquals(xy[Print].print(), "X*Y")
  }

  test("f to string with priority"){
    def f[T: Expr]: T = X * X + 2.lit * (Y + Z * X * 2.lit) - 7.lit * Z + 4.lit
    assertEquals(f[Print].print(), "X*X+2(Y+Z*X*2)-7Z+4")
  }

}
