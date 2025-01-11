extension [T](seq: IterableOnce[T]) {
  def splitBy(sep: T => Boolean): IterableOnce[List[T]] = {
    val it = seq.iterator
    def go: LazyList[List[T]] = {
      it.nextOption() match {
        case None => LazyList.empty
        case Some(x) if sep(x) => go
        case Some(x) => (x :: it.takeWhile(!sep(_)).toList) #:: go
      }
    }
    go
  }
}