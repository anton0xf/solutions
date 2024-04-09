package unit2.lesson3
// step 5: https://stepik.org/lesson/106491/step/5?unit=81017

object Test extends App {
  val x = 5
  val y = {
    val x = 7
    x + 3
  }
  println(x + "," + y)
}
