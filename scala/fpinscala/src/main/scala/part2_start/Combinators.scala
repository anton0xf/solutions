package part2_start

object Combinators {
  def curry[A, B, C](f: (A, B) => C): A => B => C = a => b => f(a, b)
  def uncurry[A, B, C](f: A => B => C): (A, B) => C = (a, b) => f(a)(b)
  def compose[A, B, C](f: B => C, g: A => B): A => C = x => f(g(x))
}
