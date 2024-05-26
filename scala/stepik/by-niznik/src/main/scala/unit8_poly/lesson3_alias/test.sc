// https://stepik.org/lesson/106534/step/4?unit=81060

type Row = List[Int]
object Row {
  def apply(elems: Int*): Row = List[Int](elems: _*)
}
val row: Row = Row(1, 2, 3)
println(row.mkString(","))

// https://stepik.org/lesson/106534/step/5?unit=81060
// see Vect
import unit8_poly.lesson3_alias.BoolVect8
(-1).toByte
(-1).toByte.toBinaryString
BoolVect8(-1).values
BoolVect8(-1).get(0)
13.toByte >> 0
-1.toByte >> 0
(-1.toByte >> 0) % 2