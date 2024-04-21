// https://stepik.org/lesson/106540/step/5?unit=81066

import scala.annotation.tailrec
import scala.util.Random
val randomList =
  List.fill(Random.nextInt(100))(Random.nextInt(1000))

// not a tailrec
def mergeNTR(xs: List[Int], ys: List[Int]): List[Int] =
  (xs, ys) match {
    case (Nil, ys) => ys
    case (xs, Nil) => xs
    case (x :: xt, y :: yt) =>
      if (x > y) y :: mergeNTR(xs, yt)
      else x :: mergeNTR(xt, ys)
  }

def merge(xs: List[Int], ys: List[Int]): List[Int] = {
  @tailrec
  def go(xs: List[Int], ys: List[Int], acc: List[Int]): List[Int] =
    (xs, ys) match {
      case (Nil, ys) => acc.reverse ++ ys
      case (xs, Nil) => acc.reverse ++ xs
      case (x :: xt, y :: yt) =>
        if (x > y) go(xs, yt, y :: acc)
        else go(xt, ys, x :: acc)
    }
  go(xs, ys, Nil)
}

//def mergeSort(xs: List[Int]): List[Int] = {
//  if (xs.length < 2) xs
//  else {
//    val (xs1, xs2) = xs.splitAt(xs.length / 2)
//    merge(mergeSort(xs1), mergeSort(xs2))
//  }
//}

def binReduce[A](zero: A, f: (A, A) => A, xs: List[A]): A = {
  @tailrec
  def go(xs: List[A], acc: List[A]): List[A] = xs match {
    case Nil              => acc
    case x :: Nil         => x :: acc
    case x1 :: x2 :: rest => go(rest, f(x1, x2) :: acc)
  }
  @tailrec
  def run(xs: List[A]): A = go(xs, Nil) match {
    case Nil      => zero
    case x :: Nil => x
    case ys       => run(ys)
  }
  run(xs)
}

def mergeSort(xs: List[Int]): List[Int] = {
  def mergeSortLevel(xs1: List[Int], xs2: List[Int]): List[Int] =
    merge(mergeSort(xs1), mergeSort(xs2))

  if (xs.length < 2) xs
  else binReduce(Nil, mergeSortLevel, xs.map(List(_)))
}

val sortedList = mergeSort(randomList)

sortedList == randomList.sorted

// https://stepik.org/lesson/106540/step/6?unit=81066
val ints = List(0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0)
val (zeros, ones) = ints.partition(_ == 0)
zeros.mkString(",")