package part3

// https://stepik.org/lesson/1437502/step/4?unit=1456113
object Step_3_6_4 {
  class Person(val name: String) {
    def unary_+ : Person = new Person(s"$name NoSurname")
  }

  def main(args: Array[String]): Unit = {
    val bob = new Person("Bob")
    println((+bob).name) // Bob NoSurname

    val alice = new Person("Alice")
    println((+alice).name) // Alice NoSurname
  }
}