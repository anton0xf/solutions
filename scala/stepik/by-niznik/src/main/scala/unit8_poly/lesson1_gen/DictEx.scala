package unit8_poly.lesson1_gen

trait DictItem[K] {
  def key: K
  def value: String
}

case class DictEx[K, I <: DictItem[K]](items: List[I]) {
  def head: I = items.head
  def map(f: String => String): DictEx[K, ADictItem[K]] =
    DictEx(items.map {item => ADictItem(item.key, f(item.value))})
  def +:[J >: I <: DictItem[K]](item: J): DictEx[K, J] = DictEx(item :: items)
}

object DictEx {
  def apply[K, I <: DictItem[K]](items: I*): DictEx[K, I] =
    DictEx(items.toList)
}

case class ADictItem[K](key: K, value: String) extends DictItem[K]
case class TDictItem[K](p: (K, String)) extends DictItem[K] {
  override def key: K = p._1
  override def value: String = p._2
}