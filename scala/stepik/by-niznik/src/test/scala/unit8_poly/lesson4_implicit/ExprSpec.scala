package unit8_poly.lesson4_implicit

import munit.FunSuite
import ExprSyntax._

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
}
