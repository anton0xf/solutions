package unit3.lesson3
// step 4: https://stepik.org/lesson/106500/step/4?unit=81026

object Strings {
  def isCapital(word: String, pos: Int): Boolean = {
    val n = word.charAt(pos).toInt
    65 <= n && n <= 90
  }
}
