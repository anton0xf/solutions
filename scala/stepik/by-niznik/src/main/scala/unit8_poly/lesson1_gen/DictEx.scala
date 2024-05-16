package unit8_poly.lesson1_gen
// https://stepik.org/lesson/106542/step/2?unit=81068

trait DictItem[K, V] {
  def key: K
  def value: V
}

case class DictEx[K, V, I <: DictItem[K, V]](items: List[I]) {
  def head: I = items.head
  def map[U](f: V => U): DictEx[K, U, ADictItem[K, U]] =
    DictEx(items.map {item => ADictItem(item.key, f(item.value))})
}

object DictEx {
  def apply[K, V, I <: DictItem[K, V]](items: I*): DictEx[K, V, I] =
    DictEx(items.toList)
}

case class ADictItem[K, V](key: K, value: V) extends DictItem[K, V]
case class TDictItem[K, V](p: (K, V)) extends DictItem[K, V] {
  override def key: K = p._1
  override def value: V = p._2
}