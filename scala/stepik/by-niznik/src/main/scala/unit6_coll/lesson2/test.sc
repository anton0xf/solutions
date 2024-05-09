// https://stepik.org/lesson/106520/step/3?unit=81046
val list = List(1, 2, 3)
list.take(1)
list(1)
list.apply(1)
// list.get(1)

// https://stepik.org/lesson/106520/step/4?unit=81046
def isPrime(n: Int): Boolean = (2 until n).filter(p => p*p <= n).forall(p => n % p != 0)

(1 to 20).filter(isPrime)

List(1, 2, 3) zip List('a', 'b', 'c')
(List(1, 2, 3) lazyZip List('a', 'b', 'c')).toList
(1, 'a').swap