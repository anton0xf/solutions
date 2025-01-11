import scala.annotation.tailrec
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day25 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day25_code_chronicle/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"locks count: ${input.locks.size}, keys count: ${input.keys.size}")
      println(s"part 1: ${solution1(input)}")
    }.get
  }

  enum Schema {
    case Lock(pins: List[Int])
    case Key(pins: List[Int])
  }
  import Schema.*

  case class Input(maxPins: Int, schemas: List[Schema]) {
    def locks: List[Lock] = schemas.collect { case x: Lock => x }
    def keys: List[Key] = schemas.collect { case x: Key => x }
  }

  def parseInput(lines: IterableOnce[String]): Input = {
    val ps = lines.splitBy(_.isEmpty).iterator.map(parseSchema).toList
    assert(ps.forall(_._1 == ps.head._1))
    Input(ps.head._1, ps.map(_._2))
  }

  def parseSchema(lines: List[String]): (Int, Schema) = {
    val head = lines.head
    assert(lines.forall(_.length == head.length))
    (lines.size - 2, if head(0) == '#' then parseLock(lines) else parseKey(lines))
  }

  def parseLock(lines: List[String]): Lock = {
    assert(lines.head.forall(_ == '#'))
    assert(lines.last.forall(_ == '.'))
    Lock(countPins(lines.tail.dropRight(1)))
  }

  def parseKey(lines: List[String]): Key = {
    assert(lines.head.forall(_ == '.'))
    assert(lines.last.forall(_ == '#'))
    Key(countPins(lines.tail.dropRight(1)))
  }

  def countPins(lines: List[String]): List[Int] =
    (0 until lines.head.length).toList.map(i => lines.count(_(i) == '#'))

  // part 1
  def solution1(input: Input): Int = {
    val locksFstPins: Map[Int, List[Lock]] = input.locks.groupBy(_.pins.head)
    input.keys.flatMap { key =>
      (key.pins.head to input.maxPins).map { pins =>
        locksFstPins
          .get(input.maxPins - pins)
          .map(_.count(matches(input.maxPins)(key)))
          .getOrElse(0)
      }
    }.sum
  }

  def matches(maxPins: Int)(key: Key)(lock: Lock): Boolean =
    (key.pins zip lock.pins).forall((p, q) => p + q <= maxPins)

  // part 2

}
