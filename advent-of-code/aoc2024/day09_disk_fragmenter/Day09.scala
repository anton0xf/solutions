import scala.collection.immutable
import scala.util.Using
import scala.io.Source
import scala.annotation.tailrec

object Day09 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day09_disk_fragmenter/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
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
    res
      .takeWhile(_.isInstanceOf[Block.File])
      .zipWithIndex
      .map {
        case (Block.File(id), i) => BigInt(id) * i
        case (block, i)          => throw new Exception(s"Unexpected block $block at position $i")
      }
      .sum
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

  // part 2
}
