// https://stepik.org/lesson/106532/step/6?unit=81058
{
  def f[T](x: T): Unit = println("ignored")
  f("WAAA!!!")
}

{
  def f[T](data: Seq[T]): List[T] = data.toList
  val x: Int = f(Seq(1, 2, 3)).head
  x
}

{
  import scala.collection.immutable.ArraySeq
  def f[M <: IndexedSeq[_]](data: M): Unit = println(data.head)
  f(ArraySeq(1,2,3))
}