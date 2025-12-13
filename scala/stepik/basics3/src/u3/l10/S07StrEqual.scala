package u3.l10

object S07StrEqual {
  @scala.annotation.tailrec
  def areEqual(str1: String, str2: String): Boolean = 
    (str1.isEmpty, str2.isEmpty) match {
      case (true, true)   => true
      case (false, false) => str1.head == str2.head && areEqual(str1.tail, str2.tail)
      case _              => false
    }
}
