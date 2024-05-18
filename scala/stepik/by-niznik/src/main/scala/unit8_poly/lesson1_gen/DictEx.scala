package unit8_poly.lesson1_gen

trait DictItem[+K, +V] {
  def key: K
  def value: V
}

case class DictEx[K, V, I[+X, +Y] <: DictItem[X, Y]](items: List[I[K, V]]) {
  def head: I[K, V] = items.head
  def map[U, J[+X, +Y] >: ADictItem[X, Y] <: DictItem[X, Y]](f: V => U): DictEx[K, U, J] = {
    val newItems: List[J[K, U]] = items.map { item: I[K, V] =>
      val value: V = item.value
      val newItem: J[K, U] = ADictItem[K, U](item.key, f(value))
      newItem
    }
    DictEx[K, U, J](newItems)
  }
  def +:[U >: V, J[+X, +Y] >: I[X, Y] <: DictItem[X, Y]](item: J[K, U]): DictEx[K, U, J] = {
    val item1: J[K, U] = item
    val newItems: List[J[K, U]] = item1 :: items
    DictEx[K, U, J](newItems)
  }
}

object DictEx {
  def make[K, V, I[+X, +Y] <: DictItem[X, Y]](items: I[K, V]*): DictEx[K, V, I] =
    DictEx[K, V, I](items.toList)
}

case class ADictItem[+K, +V](key: K, value: V) extends DictItem[K, V]
case class TDictItem[+K, +V](p: (K, V)) extends DictItem[K, V] {
  override def key: K = p._1
  override def value: V = p._2
}
