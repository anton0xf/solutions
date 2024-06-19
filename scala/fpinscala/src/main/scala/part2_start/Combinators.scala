package part2_start

object Combinators {
  def curry[A, B, C](f: (A, B) => C): A => (B => C) = a => b => f(a, b)
}
