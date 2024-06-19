BigInt(-1).gcd(BigInt(-5))

import unit8_poly.lesson4_implicit.Ratio.RatioOps

4.\\(-6)

import unit8_poly.lesson4_implicit.Expr
import unit8_poly.lesson4_implicit.ExprSyntax._

def x[T](implicit expr: Expr[T]): T = X
val xStr: String = x

def one[T: Expr]: T = 1.lit
val oneStr: String = one

def xPlusOne[T: Expr]: T = X + 1.lit
val xPlusOneStr: String = xPlusOne

def f[T: Expr]: T = X * X + 2.lit * (Y + Z * X * 2.lit) - 7.lit * Z + 4.lit
val fStr: String = f