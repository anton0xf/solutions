package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/7?unit=81046

/*
Считайте числа из консоли до слова END.
С полученным списком необходимо выполнить:
 1. выбрать каждый второй элемент
 2. каждый выбранный элемент умножить на 2
 3. вывести в консоль сумму элементов полученного списка
 */

import scala.io.StdIn

object SumFilteredInts {
  def main(args: Array[String]): Unit = {
    val lines = LazyList.continually(StdIn.readLine())
    println(filteredSum(lines))
  }

  def filteredSum(lines: Seq[String]): Int = {
    lines.takeWhile(_ != "END")
      .map(_.toInt)
      .zipWithIndex
      .filter(_._2 % 2 == 1)
      .map(_._1 * 2)
      .sum
  }
}
