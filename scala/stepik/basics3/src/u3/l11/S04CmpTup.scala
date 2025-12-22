package u3.l11

object S04CmpTup {

  private def f(arg1: Char, arg2: Char): Unit = {
    val tuple = List[(Char, Char) => Boolean]((_ == _), (_ != _), (_ > _), (_ >= _), (_ < _), (_ <= _))
    val res = tuple.map(f => f(arg1, arg2))
    println(res.mkString("(", ",", ")"))
    Date
  }

  @main
  def main(): Unit = {
    f('a', 'b')
  }
}
