package part4

object Step_4_8_4 {
  def countChars(s: String): Map[Char, Int] = s.toLowerCase.groupBy(identity).mapValues(_.length)
}