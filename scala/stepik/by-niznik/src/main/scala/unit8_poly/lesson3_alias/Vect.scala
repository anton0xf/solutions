package unit8_poly.lesson3_alias
// https://stepik.org/lesson/106534/step/5?unit=81060

import unit8_poly.lesson3_alias.Vect.Aux

trait Vect extends Any {
  type Item
  def length: Int
  def get(index: Int): Item
  def set(index: Int, item: Item): Aux[Item]
}

object Vect {
  type Aux[I] = Vect { type Item = I }
  def toList(vect: Vect): List[vect.Item] = (0 until vect.length).map(vect.get).toList
  def toBoolList(vect: Vect { type Item = Boolean }): String = toList(vect).map {
    case true  => 1
    case false => 0
  }.mkString
}

final case class StringVect(str: String) extends AnyVal with Vect {
  type Item = Char
  def length: Int = str.length
  def get(index: Int): Char = str.charAt(index)
  def set(index: Int, item: Char): Aux[Char] = StringVect(str.updated(index, item))
}

final case class BoolVect64(values: Long) extends AnyVal with Vect {
  type Item = Boolean
  def length = 64
  def get(index: Int): Boolean = (values >> index) % 2 != 0
  def set(index: Int, item: Boolean): Aux[Boolean] =
    if (index >= length || index < 0) this
    else {
      val d = 1L << index
      val newValues = if (item) values | d else values & ~d
      BoolVect64(newValues)
    }
}

final case class BoolVect8(values: Byte) extends AnyVal with Vect {
  type Item = Boolean
  def length = 8
  def get(index: Int): Boolean = (values >> index) % 2 != 0
  def set(index: Int, item: Boolean): Aux[Boolean] = {
    val d = (1 << index).toByte
    val newValues = if (item) values | d else values & ~d
    BoolVect8(newValues.toByte)
  }
}
