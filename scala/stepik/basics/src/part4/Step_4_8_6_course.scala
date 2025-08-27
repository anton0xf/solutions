import scala.util.Try

object Step_4_8_6_course {

  def main(args: Array[String]): Unit = {
    Try(LoginService.login())
      .flatMap(platform => Try(platform.enroll()))
      .fold(
        e => println(e.getMessage),
        NotificationService.notify,
      )
  }

  object LoginService {
    def login(): Platform = new Platform {
      override def enroll(): String = "Scala"
    }
  }

  trait Platform {
    def enroll(): String
  }

  object NotificationService {
    def notify(course: String): Unit = println(
      s"You have successfully enrolled in the course $course"
    )
  }

}
