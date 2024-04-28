package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/4?unit=81046

object Primes {
  def isPrime(n: Int): Boolean = (2 until n).filter(p => p*p <= n).forall(p => n % p != 0)
}
