package part4

object Step_4_6_8 {
  private def longComputation(): Int = {
    println("long computation")
    100
  }

  def main(args: Array[String]): Unit = {
    lazy val x = longComputation()
    println("preparing")
    println(x + x)
  }
}
