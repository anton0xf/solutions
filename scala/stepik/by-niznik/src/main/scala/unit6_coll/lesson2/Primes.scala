package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/4?unit=81046

object Primes {
  def isPrime(n: Int): Boolean = LazyList.from(2)
    .takeWhile(p => p * p <= n).forall(n % _ != 0)
  lazy val list: LazyList[Int] = 2 #:: LazyList.from(3, 2).filter(isPrime)
}
