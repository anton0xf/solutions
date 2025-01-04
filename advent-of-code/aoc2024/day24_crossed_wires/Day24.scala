import scala.annotation.tailrec
import scala.collection.immutable
import scala.util.Using
import scala.io.Source

object Day24 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day24_crossed_wires/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
    }
  }

  case class Input(wires: Map[String, Boolean], gates: List[Gate])
  case class Gate(op: Op, inA: String, inB: String, out: String)
  sealed trait Op {
    def eval(a: Boolean, b: Boolean): Boolean
  }

  object Op {
    case object And extends Op:
      def eval(a: Boolean, b: Boolean): Boolean = a && b

    case object Or extends Op:
      def eval(a: Boolean, b: Boolean): Boolean = a || b

    case object Xor extends Op:
      def eval(a: Boolean, b: Boolean): Boolean = a ^ b
  }

  def parseInput(lines: IterableOnce[String]): Input = {
    val (wireLines, gateLines) = lines.iterator.dropWhile(_.isEmpty).span(_.nonEmpty)
    Input(
      wires = wireLines.map { line =>
        line.split(":\\s+") match
          case Array(wire, state) => wire -> toBool(state)
          case _                  => throw new Exception(s"unexpected wire line: $line")
      }.toMap,
      gates = gateLines
        .filterNot(_.isBlank)
        .map { line =>
          line.split(' ') match
            case Array(a, op, b, "->", res) => Gate(toOp(op), a, b, res)
            case _                          => throw new Exception(s"unexpected gate line: $line")
        }
        .toList
    )
  }

  def toBool(s: String): Boolean = s match
    case "0" => false
    case "1" => true
    case _   => throw new Exception(s"unexpected wire state: $s")

  def toOp(s: String): Op = s match
    case "AND" => Op.And
    case "OR"  => Op.Or
    case "XOR" => Op.Xor

  // part 1
  def solution1(input: Input): BigInt = {
    // println(input)
    val wires = simulate(input)
    val bits = wires.iterator
      .filter { (wire, _) => wire.startsWith("z") }
      .map { (wire, state) => (wire.substring(1).toInt, state) }
      .toVector
      .sortBy(_._1)
      .map(_._2)
    toNum(bits)
  }

  def simulate(input: Input): Map[String, Boolean] = {
    @tailrec
    def go(
        wires: Map[String, Boolean],
        changed: Boolean,
        gates1: List[Gate],
        gates2: List[Gate]
    ): Map[String, Boolean] = gates1 match {
      case Nil => if changed && gates2.nonEmpty then go(wires, false, gates2, Nil) else wires
      case gate :: gates1 =>
        (for {
          a <- wires.get(gate.inA)
          b <- wires.get(gate.inB)
        } yield gate.out -> gate.op.eval(a, b)) match {
          case None                => go(wires, changed, gates1, gate :: gates2)
          case Some(wire -> state) => go(wires.updated(wire, state), true, gates1, gates2)
        }
    }
    go(input.wires, false, input.gates, Nil)
  }

  /** Get integer number from sequence of its bits from the least significant to most significant. <br\> For example
    * <code>toNum(Seq(false, true, true)) == 6</code>
    */
  def toNum(bools: Seq[Boolean]): BigInt = {
    @tailrec
    def go(bools: Seq[Boolean], n: BigInt): BigInt = bools match {
      case Seq()          => n
      case false +: bools => go(bools, n * 2)
      case true +: bools  => go(bools, n * 2 + 1)
    }
    go(bools.reverse, 0)
  }

  // part 2
}
