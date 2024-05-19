// https://stepik.org/lesson/106534/step/4?unit=81060

type Row = List[Int]
object Row {
  def apply(elems: Int*): Row = List[Int](elems: _*)
}
val row: Row = Row(1, 2, 3)
println(row.mkString(","))