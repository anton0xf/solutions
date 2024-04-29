package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/4?unit=81046

object Primes {
  def isPrime(n: Long): Boolean = LazyList.iterate(2L)(_ + 1L)
    .takeWhile(p => p * p <= n).forall(n % _ != 0)
  lazy val list: LazyList[Long] = 2 #:: LazyList.iterate(3L)(_ + 2).filter(isPrime)
}
