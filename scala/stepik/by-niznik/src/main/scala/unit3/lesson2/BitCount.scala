package unit3.lesson2
// step 5: https://stepik.org/lesson/106498/step/5

object BitCount {
  def count(n: Int): Int = if (n == 0) 0 else n % 2 + count(n / 2)

  def main(args: Array[String]): Unit = {
    import scala.io.StdIn
    println(count(StdIn.readInt()))
  }
}
