package part4

object Step_4_7_11 {

  trait SeniorityLevel

  private object SeniorityLevel {
    case object Junior extends SeniorityLevel

    case object Middle extends SeniorityLevel

    case object Senior extends SeniorityLevel
  }

  private case class Developer(
      name: String,
      level: SeniorityLevel,
      progLanguage: List[String]
  )

  def main(args: Array[String]): Unit = {
    val developers: List[Developer] = List(
      Developer(name = "dev1", level = SeniorityLevel.Junior, progLanguage = List("lang1")),
      Developer(name = "dev2", level = SeniorityLevel.Middle, progLanguage = List("lang1")),
      Developer(name = "dev3", level = SeniorityLevel.Senior, progLanguage = List("lang1", "lang2")),
      Developer(name = "dev4", level = SeniorityLevel.Middle, progLanguage = List("lang1", "lang2", "lang3")),
      Developer(name = "dev5", level = SeniorityLevel.Senior, progLanguage = List("lang1", "lang2", "lang3", "lang4")),
    )
    //  найти имена разработчиков уровня Middle или Senior, знающих минимум три языка программирования
    val foundDevs: List[String] = developers
      .filter(dev => dev.level == SeniorityLevel.Middle || dev.level == SeniorityLevel.Senior)
      .filter(dev => dev.progLanguage.size >= 3)
      .map(_.name)
    println(foundDevs) // => List(dev4, dev5)
  }
}
