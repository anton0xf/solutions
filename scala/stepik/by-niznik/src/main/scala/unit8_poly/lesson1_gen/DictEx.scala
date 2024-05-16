package unit8_poly.lesson1_gen

trait DictItem {
  def key: Int
  def value: String
}

case class DictEx[I <: DictItem](items: List[I]) {
  def head: I = items.head
  def map(f: String => String): DictEx[ADictItem] =
    DictEx(items.map {item => ADictItem(item.key, f(item.value))})
  def +:[J >: I <: DictItem](item: J): DictEx[J] = DictEx(item :: items)
}

object DictEx {
  def apply[I <: DictItem](items: I*): DictEx[I] =
    DictEx(items.toList)
}

case class ADictItem(key: Int, value: String) extends DictItem
case class TDictItem(p: (Int, String)) extends DictItem {
  override def key: Int = p._1
  override def value: String = p._2
}