import scala.collection.immutable
import scala.util.Using
import scala.io.Source
import scala.annotation.tailrec

object Day09 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day09_disk_fragmenter/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  type Input = String
  enum Block:
    case Free
    case File(id: Int)

  def showBlocks(blocks: Vector[Block]): String = blocks.map {
    case Block.Free     => "."
    case Block.File(id) => id.toString()
  }.mkString

  def parseInput(lines: Iterator[String]): Input = lines.next()

  // part 1
  def solution1(input: Input): BigInt = {
    val src: Vector[Block] = toBlocks(input)
    val res: Vector[Block] = compact(src)
    summarize(res.takeWhile(_.isInstanceOf[Block.File]))
  }

  def toBlocks(input: String): Vector[Block] = {
    @tailrec
    def go(id: Int, free: Boolean, chars: List[Char], acc: Vector[Block]): Vector[Block] =
      chars match {
        case Nil => acc
        case ch :: chars =>
          go(
            id = if free then id else id + 1,
            free = !free,
            chars = chars,
            acc = acc ++ Vector.fill(ch.toString().toInt) {
              if free then Block.Free else Block.File(id)
            }
          )
      }
    go(id = 0, free = false, chars = input.toList, acc = Vector())
  }

  def compact(blocks: Vector[Block]): Vector[Block] = {
    @tailrec
    def go(blocks: Vector[Block], i: Int, j: Int): Vector[Block] = {
      if i == j then blocks
      else
        blocks(j) match {
          case Block.Free => go(blocks, i, j - 1)
          case jb @ Block.File(id) =>
            blocks(i) match {
              case Block.File(_) => go(blocks, i + 1, j)
              case Block.Free    => go(blocks.updated(i, jb).updated(j, Block.Free), i + 1, j - 1)
            }
        }
    }
    go(blocks, 0, blocks.size - 1)
  }

  def summarize(blocks: Vector[Block]) = {
    blocks.zipWithIndex.map {
      case (Block.File(id), i) => BigInt(id) * i
      case _                   => BigInt(0)
    }.sum
  }

  // part 2
  enum Span(size: Int):
    case Free(size: Int) extends Span(size)
    case File(id: Int, size: Int) extends Span(size)

  def solution2(input: Input): BigInt = {
    val src: Vector[Span] = toSpans(input)
    val res: Vector[Span] = compact2(src)
    summarize(toBlocks(res))
  }

  def toSpans(input: String): Vector[Span] = {
    @tailrec
    def go(id: Int, free: Boolean, chars: List[Char], acc: Vector[Span]): Vector[Span] =
      chars match {
        case Nil => acc
        case ch :: chars =>
          val size = ch.toString().toInt
          go(
            id = if free then id else id + 1,
            free = !free,
            chars = chars,
            acc = acc :+ (if free then Span.Free(size) else Span.File(id, size))
          )
      }
    go(id = 0, free = false, chars = input.toList, acc = Vector())
  }

  def compact2(spans: Vector[Span]): Vector[Span] = {
    @tailrec
    def go(spans: Vector[Span], j: Int): Vector[Span] = {
      if j == 0 then spans
      else
        spans(j) match {
          case Span.Free(_) => go(spans, j - 1)
          case file @ Span.File(_, size) => {
            val newSpans = spans
              .slice(0, j)
              .zipWithIndex
              .find {
                case (Span.Free(space), _) => size <= space
                case _                     => false
              }
              .map {
                case (Span.Free(space), i) =>
                  val insert =
                    if space == size then Seq(file) else Seq(file, Span.Free(space - size))
                  spans.slice(0, i) ++ insert ++ spans.slice(i + 1, j) ++
                    Seq(Span.Free(size)) ++ spans.slice(j + 1, spans.size)
                case span => throw new Exception(s"unexpected span: $span")
              }
              .getOrElse(spans)
            go(newSpans, j - 1)
          }
        }
    }
    go(spans, spans.size - 1)
  }

  def toBlocks(spans: Vector[Span]): Vector[Block] = spans.foldLeft(Vector()) { (acc, span) =>
    acc ++ (span match {
      case Span.Free(size)     => Vector.fill(size)(Block.Free)
      case Span.File(id, size) => Vector.fill(size)(Block.File(id))
    })
  }

}
