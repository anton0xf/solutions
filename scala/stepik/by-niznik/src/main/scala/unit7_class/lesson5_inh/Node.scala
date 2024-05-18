package unit7_class.lesson5_inh
// https://stepik.org/lesson/106527/step/3?unit=81053

sealed trait Node[A] {
  def values: List[A] = this match {
    case Leaf(value) => List(value)
    case Branch(left, right) => left.values ::: right.values
  }
  def +:(value: A): Node[A] = this match {
    case Leaf(_) => Branch(Leaf(value), this)
    case Branch(left, right) => Branch(value +: left, right)
  }
  def :+(value: A): Node[A] = this match {
    case Leaf(_) => Branch(this, Leaf(value))
    case Branch(left, right) => Branch(left, right :+ value)
  }
  def ++(other: Node[A]): Node[A] = Branch(this, other)
}

case class Leaf[A](value: A) extends Node[A]
case class Branch[A](left: Node[A], right: Node[A]) extends Node[A]
