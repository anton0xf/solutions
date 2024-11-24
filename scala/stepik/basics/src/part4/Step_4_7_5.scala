package part4

object Step_4_7_5 {
  case class Course(id: Int, title: String)

  case class Error(id: Int, message: String)

  def main(args: Array[String]): Unit = {
    val in: List[Either[Error, Course]] = List(
      Left(Error(1, "err")),
      Right(Course(1, "Scala")),
      Right(Course(1, "asdf")),
      Right(Course(2, "Scala For Beginners")),
      Right(Course(3, "Learn Scala"))
    )
    val res = in.flatMap(_.toSeq).filter(_.title.contains("Scala"))
    res.foreach(println)
  }
}
