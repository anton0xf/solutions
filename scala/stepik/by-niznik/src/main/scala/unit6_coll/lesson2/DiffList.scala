package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/10?auth=login&unit=81046

abstract class DiffList[A](calculate: List[A] => List[A]) {
  def prepend(s: List[A]): DiffList[A]
  def append(s: List[A]): DiffList[A]
  def result: List[A]
}

class DiffListImpl[A] (f: List[A] => List[A]) extends DiffList[A](f) {
  override def prepend(s: List[A]): DiffList[A] = new DiffListImpl[A](xs => s ++ f(xs))
  override def append(s: List[A]): DiffList[A] = new DiffListImpl[A](xs => f(xs) ++ s)
  override def result: List[A] = f(Nil)
}