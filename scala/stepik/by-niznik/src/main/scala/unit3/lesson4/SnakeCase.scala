package unit3.lesson4
// step 5: https://stepik.org/lesson/106501/step/5?auth=login&unit=81027

import scala.io.StdIn

object SnakeCase {
  def main(args: Array[String]): Unit = {
    val str = StdIn.readLine()
    println(if (check(str)) "true" else "false")
  }
  def check(str: String): Boolean = {
    str.matches("([a-z]+_)*[a-z]+")
  }
}
