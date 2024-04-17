package unit5.lesson2
// step 5: https://stepik.org/lesson/106510/step/5?unit=81036
/*
Известно, что все, кто говорит "meow" или "nya" - кошки, все, кого зовут "Rex" - собаки,
а цифры "0" или "1" (обратите внимание, что нужно проверять наличие символов, а не целочисленных типов)
в строке says есть только у роботов. (Кошек и роботов не могут звать "Rex", собаки не мяукают)

Используя pattern-matching, определите вид питомца в переменной pet.
Выведите "cat" для кошек, "dog" для собак, "robot" для роботов и "unknown" иначе.
 */
case class Pet(name: String, says: String)

object PetSay {
  def main(args: Array[String]): Unit = {
    val pet = Pet("My cat", "meow")
    val kind = petKind(pet)
    println(s"$pet is $kind")
  }

  def petKind(pet: Pet): String = {
    val robotSays = ".*[01].*".r
    pet match {
      case Pet(_, "meow" | "nya") => "cat"
      case Pet("Rex", _) => "dog"
      case Pet(_, robotSays()) => "robot"
      case _ => "unknown"
    }
  }
}
