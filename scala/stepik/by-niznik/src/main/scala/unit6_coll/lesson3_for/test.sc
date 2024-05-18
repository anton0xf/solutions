// https://stepik.org/lesson/106522/step/7?unit=81048
// for { x <- Some(2); y <- List(1,2,3,4) } yield x + y
for { (k,v) <- Map("a" -> 1, "b" -> 2) } yield k
for { x <- List(1,2,3,4) } x
// for { x <- Some(1) ; y <- Left("year") } yield x + y
for { x <- Some(1) ; y <- None } yield (x, y)