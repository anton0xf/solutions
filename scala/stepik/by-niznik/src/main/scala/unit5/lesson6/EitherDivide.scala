package unit5.lesson6
// step 7: https://stepik.org/lesson/106517/step/7?unit=81043

/*
Правильной называется дробь, у которой модуль числителя  меньше модуля знаменателя.
Будем представлять дробь парой (числитель, знаменатель).

Реализуйте операцию деления divide(p: (Int, Int))(q: (Int, Int)): Either[String, (Int, Int)],
возвращающую результат деления p на q или текст ошибки.
Проверьте корректность входных данных, если входные дроби неправильные, верните ошибку Left("Invalid input").
Если делитель нулевой, верните Left("Zero divisor").
Если в результате получилась неправильная дробь, ошибка Left("Improper result").

Сократите результат до простой дроби. Воспользуйтесь алгоритмом Евклида, разобранным в модуле про кортежи, или методом BigInt.gcd .
 */

import java.lang.Math.abs

object EitherDivide {
  def divide(p: (Int, Int))(q: (Int, Int)): Either[String, (Int, Int)] = {
    (for {
      _ <- checkInput(p)
      _ <- checkInput(q).filterOrElse(_._1 != 0, "Zero divisor")
    } yield (p._1 * q._2, p._2 * q._1))
      .filterOrElse(isRight, "Improper result")
      .map(simplify)
  }

  def checkInput(p: (Int, Int)): Either[String, (Int, Int)] =
    Right(p)
      .filterOrElse(_._2 != 0, "Zero divisor")
      .filterOrElse(isRight, "Invalid input")

  def isRight(p: (Int, Int)): Boolean = abs(p._1) < abs(p._2)

  def simplify(p: (Int, Int)): (Int, Int) = {
    val d = BigInt(p._1).gcd(p._2).intValue
    (p._1 / d, p._2 / d)
  }
}
