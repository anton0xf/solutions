package unit4.lesson2
// step 5: https://stepik.org/lesson/106506/step/5?auth=login&unit=81032
object LessonDataSearch {
  val searchOdd = (array: List[Int]) => LessonData.searchInArray(_ % 2 == 1, array)

  def main(args: Array[String]): Unit = {
    println(searchOdd(List(8,11,12))) // List(11)
  }
}

object LessonData{
  def searchInArray(cond: Int => Boolean, array: List[Int]): List[Int] = {
    array.filter(cond)
  }
}
