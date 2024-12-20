import scala.annotation.tailrec
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day17 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day17_chronospatial_computer/input")) { source =>
      val computer = parseInput(source.getLines())
      println(s"part 1: ${solution1(computer)}")
      println(s"part 2: ${solution2(computer)}")
    }
  }

  case class Computer(
      program: Vector[Int],
      a: BigInt,
      b: BigInt,
      c: BigInt,
      ip: Int = 0,
      out: Vector[Int] = Vector()
  ) {
    def literalOp: Option[Int] = program.lift(ip + 1).map { x =>
      assert((0 to 7).contains(x))
      x
    }

    def comboOp: Option[BigInt] = program.lift(ip + 1).map { x =>
      assert((0 to 6).contains(x))
      if (0 to 3).contains(x) then x
      else if x == 4 then a
      else if x == 5 then b
      else {
        assert(x == 6); c
      }
    }

    val cmds: Map[Int, String] = Map(
      0 -> "adv",
      1 -> "bxl",
      2 -> "bst",
      3 -> "jnz",
      4 -> "bxc",
      5 -> "out",
      6 -> "bdv",
      7 -> "cdv"
    )

    def tick: Option[Computer] = program.lift(ip).flatMap {
      // adv
      case 0 => comboOp.map { op => copy(ip = ip + 2, a = a >> op.toInt) }
      // bxl
      case 1 => literalOp.map { op => copy(ip = ip + 2, b = b ^ op) }
      // bst
      case 2 => comboOp.map { op => copy(ip = ip + 2, b = op % 8) }
      // jnz
      case 3 => if a == 0 then Some(copy(ip = ip + 2)) else literalOp.map { op => copy(ip = op) }
      // bxc
      case 4 => literalOp.map { _ => copy(ip = ip + 2, b = b ^ c) }
      // out
      case 5 => comboOp.map { op => copy(ip = ip + 2, out = out :+ (op % 8).toInt) }
      // bdv
      case 6 => comboOp.map { op => copy(ip = ip + 2, b = a >> op.toInt) }
      // cdv
      case 7 => comboOp.map { op => copy(ip = ip + 2, c = a >> op.toInt) }
    }

    def state: List[(String, BigInt)] = List("ip" -> ip, "a" -> a, "b" -> b, "c" -> c)

    @tailrec
    final def exec: Computer =
      val next = tick
      // println(s"$state ${program.lift(ip).map(cmds(_))}($literalOp) -> ${next.map(_.state)}")
      if next.isDefined then next.get.exec else this

    def show: String =
      s"""Register A: $a
         |Register B: $b
         |Register C: $c
         |
         |Program: $showProgram
         |""".stripMargin

    def showProgram: String = program
      .grouped(2)
      .map {
        case Vector(cmd, op) => s"${cmds(cmd)}($op)"
        case v               => s"unexpected $v"
      }
      .mkString(", ")
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
    // println(computer)
    computer.exec.out.mkString(",")
  }

  // part 2
  def solution2(computer: Computer): BigInt = {
    // println(computer.show)
    // println(computer)
    def go(a1s: List[BigInt], i: Int): List[BigInt] = a1s.flatMap { a1 =>
      // println(s"a[$i] == $a1")
      if i == 0 then List(a1)
      else {
        val as = stepBack(computer, a1, computer.program(i - 1))
        go(as, i - 1)
      }
    }
    go(List(0), computer.program.size).min
  }

  def stepBack(c: Computer, a1: BigInt, p: Int): List[BigInt] = {
    val as = (0 until 8).iterator.flatMap { x =>
      val a = a1 * 8 + x
      val c1 = c.copy(a = a).exec
      if c1.out.head == p then Some(a) else None
    }.toList
    // println(s"stepBack(c, $a1, $p) = $as")
    as
  }
}
