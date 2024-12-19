import scala.annotation.tailrec
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day17 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day17_chronospatial_computer/input")) { source =>
      val computer = parseInput(source.getLines())
      println(s"part 1: ${solution1(computer)}")
    }
  }

  case class Computer(
                       program: Vector[Int], a: Int, b: Int, c: Int,
                       ip: Int = 0, out: Vector[Int] = Vector()
                     ) {
    def literalOp: Option[Int] = program.lift(ip + 1).map { x =>
      assert((0 to 7).contains(x))
      x
    }

    def comboOp: Option[Int] = program.lift(ip + 1).map { x =>
      assert((0 to 6).contains(x))
      if (0 to 3).contains(x) then x
      else if x == 4 then a
      else if x == 5 then b
      else {
        assert(x == 6); c
      }
    }

    def tick: Option[Computer] = program.lift(ip).flatMap {
      // adv
      case 0 => comboOp.map { op => copy(ip = ip + 2, a = a / (1 << op)) }
      // bxl
      case 1 => literalOp.map { op => copy(ip = ip + 2, b = b ^ op) }
      // bst
      case 2 => comboOp.map { op => copy(ip = ip + 2, b = op % 8) }
      // jnz
      case 3 => if a == 0 then Some(copy(ip = ip + 2)) else literalOp.map { op => copy(ip = op) }
      // bxc
      case 4 => literalOp.map { _ => copy(ip = ip + 2, b = b ^ c) }
      // out
      case 5 => comboOp.map { op => copy(ip = ip + 2, out = out :+ op % 8) }
      // bdv
      case 6 => comboOp.map { op => copy(ip = ip + 2, b = a / (1 << op)) }
      // cdv
      case 7 => comboOp.map { op => copy(ip = ip + 2, c = a / (1 << op)) }
    }

    final def exec: Computer = {
      val trace = LazyList.iterate[Option[Computer]](Some(this))(_.flatMap(_.tick))
      trace.takeWhile(_.isDefined).last.get
    }
  }

  def parseInput(lines: IterableOnce[String]): Computer = {
    val iter = lines.iterator
    val a = parseRegister('A', iter.next())
    val b = parseRegister('B', iter.next())
    val c = parseRegister('C', iter.next())
    assert(iter.next().isBlank)
    val program = parseProgram(iter.next())
    Computer(program, a, b, c)
  }

  def removePrefix(prefix: String, s: String): String = {
    assert(s.startsWith(prefix))
    s.substring(prefix.length)
  }

  def parseRegister(register: Char, line: String): Int =
    removePrefix(s"Register $register: ", line).toInt

  def parseProgram(line: String): Vector[Int] =
    removePrefix("Program: ", line).split(',').map(_.toInt).toVector

  // part 1
  def solution1(computer: Computer): String = {
    println(computer) // TODO remove
    computer.exec.out.mkString(",")
  }

  // part 2
}
