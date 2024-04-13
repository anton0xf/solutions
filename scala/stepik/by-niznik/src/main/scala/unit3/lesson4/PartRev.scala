package unit3.lesson4
// step 4: https://stepik.org/lesson/106501/step/4?unit=81027

import scala.io.StdIn

/**
 * Cчитайте из консоли два числа: startIndex и endIndex.
 * Они расположены в первой строке и разделены одним пробелом. Далее считайте строку str.
 *
 * Напечатайте в ответ входную строку, обратив порядок символов от startIndex до endIndex включительно.
 */
object PartRev {
  def main(args: Array[String]): Unit = {
    val Array(startIndex, endIndex): Array[Int] = StdIn.readLine().split("\\s+").map(_.toInt)
    val str: String = StdIn.readLine()
    println(reversePart(str, startIndex, endIndex))
  }

  def reversePart(str: String, startIndex: Int, endIndex: Int): String = {
    val nextIndex = endIndex + 1 // index of fist char of the second untouched part
    str.substring(0, startIndex) + str.substring(startIndex, nextIndex).reverse + str.substring(nextIndex)
  }
}
