package unit7_class.lesson3_obj
// https://stepik.org/lesson/106525/step/3?unit=81051

class Point(val x: Double, val y: Double, val z: Double) {
  def +(p: Point): Point = Point(x + p.x, y + p.y, z + p.z)
  def /(d: Double): Point = Point(x / d, y / d, z / d)
}

object Point {

  /** фабрика, принимает три координаты и возвращает экземпляр типа Point */
  def apply(x: Double, y: Double, z: Double): Point = new Point(x, y, z)

  /** принимает List[Point] и вычисляет усреднённую точку между всеми координатами,
    * либо точку с началом осей координат, если её невозможно рассчитать
    */
  def average(ps: List[Point]): Point =
    if (ps.isEmpty) Point(0, 0, 0) else ps.reduce(_ + _) / ps.length

  /** принимает Point и превращает её в строку, состоящую из координат разделённых через пробел */
  def show(p: Point): String = s"${p.x} ${p.y} ${p.z}"

}
