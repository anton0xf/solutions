package part4

object Step_4_8_1 {
  case class Person(name: String)
object Person {
  def unapply(input: String): Some[String] = Some(input.split(' ') match {
      case arr@Array(_, _) => arr.map(i => s"${i.toUpperCase.head}.").mkString(" ")
      case _ => "Failed to get initials"
    })
}

  def main(args: Array[String]): Unit = {
//    val input: String = "John doe"
    val input: String = "j"
    val Person(initials) = input
    println(s"$initials")
  }
}
