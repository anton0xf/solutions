package unit8_poly.lesson2_var
// https://stepik.org/lesson/106532/step/5?unit=81058

class Person (val name: String)

class Student(name: String, val course: Int) extends Person(name)

class Pair[+T](val first: T, val second: T) {
  def replaceFirst[S >: T](newValue: S): Pair[S] = {
    new Pair(newValue, second)
  }
}

object PairEx {
  def printNames(pair: Pair[Person]): Unit = {
    println("1: " + pair.first.name + "  2: " + pair.second.name)
  }

  def main(args: Array[String]): Unit = {
    val pair: Pair[Student] = new Pair(new Student("Pavel", 1), new Student("Oleg", 5))
    printNames(pair)
    printNames(pair.replaceFirst(new Person("Oliver")))
  }
}