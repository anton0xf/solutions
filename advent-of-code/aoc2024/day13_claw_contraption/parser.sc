import scala.util.parsing.combinator.*

object InputParser extends RegexParsers {
  def num: Parser[(Int, String)] = ("""\s*num: """.r ~> """(\d+)""".r ^^ (_.toInt)) ~
    ("""\s*""".r ~> """.*""".r)
    ^^ { case n ~ r => (n, r) }
}

import InputParser.*

parse(num, "\n num: 13  asdf")
