package unit8_poly.lesson1_gen

trait DictItem[K, V] {
  def key: K
  def value: V
}

case class DictEx[K, V, I <: DictItem[K, V]](items: List[I]) {
  def head: I = items.head
  def map[U, J >: ADictItem[K, U] <: DictItem[K, U]](f: V => U): DictEx[K, U, J] =
    DictEx(items.map {item => ADictItem(item.key, f(item.value))})
  def +:[J >: I <: DictItem[K, V]](item: J): DictEx[K, V, J] = DictEx(item :: items) // TODO V => U >: V
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