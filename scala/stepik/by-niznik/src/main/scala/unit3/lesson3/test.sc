// step 2: https://stepik.org/lesson/106500/step/2?unit=81026
val qw = "qw"
"qwer" == qw + "er" // true
"qwer" eq qw + "er" // false

// step 3: https://stepik.org/lesson/106500/step/3?unit=81026
{
  val s3 = "bar"
  val s1 = "foo" + s3
  val s2 = "foo" + s3
  println(s1 == s2)
}

{
  val s1 = "foo"
  val s2 = "foo"
  println(s1 == s2)
}

{
  val s3 = "bar"
  val s1 = "foo" + s3
  val s2 = "foo" + s3
  println(s1 eq s2)
}

{
  val s1 = "foo"
  val s2 = "foo"
  println(s1 eq s2)
}

// step 4: https://stepik.org/lesson/106500/step/4?unit=81026
List('a', 'z').map(_.toInt)
List('A', 'Z').map(_.toInt)

"abc".charAt(0)
"abc".charAt(1)