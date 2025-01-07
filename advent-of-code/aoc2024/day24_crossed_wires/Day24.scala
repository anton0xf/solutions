import scala.annotation.tailrec
import scala.collection.immutable.Queue
import scala.collection.{immutable, mutable}
import scala.util.Using
import scala.io.Source

object Day24 {
  enum Wire {
    case Aux(name: String)
    case Vec(name: String, n: Int)

    override def toString: String = this match
      case Aux(name)    => name
      case Vec(name, n) => s"$name[$n]"
  }

  object Wire {
    def unapply(wire: Wire): (String, Int) = wire match
      case Aux(name)    => (name, 0)
      case Vec(name, n) => (name, n)
  }

  import Wire.{Aux, Vec}

  given Ordering[Wire] = Ordering.by(Wire.unapply)

  def selectAux(wires: Set[Wire]): Set[Aux] = wires.collect { case wire: Aux => wire }

  def selectVec(wires: Set[Wire]): Map[String, Seq[Vec]] = wires
    .collect { case wire: Vec => wire }
    .groupBy(_.name)
    .view
    .mapValues(_.toSeq.sorted)
    .toMap

  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day24_crossed_wires/input")) { source =>
      val input = parseInput(source.getLines())
      val wires: Set[Wire] = input.wires.keySet ++ input.gates.flatMap(_.wires)
      val gatesMap = gatesOutputs(input.gates)
      println(s"wires count = ${wires.size}, gates count = ${gatesMap.keySet.size}")
      println(s"wires: ${listWires(wires)}\n")
      val zs: Seq[Wire] = selectVec(wires)("z")
      // println(s"zs deps:\n${zs.map(deps(gatesMap)).mkString("\n")}\n")

      val ds = wires.toSeq.sorted.map(wire => wire -> deps(gatesMap)(wire))
      // println(s"deps:\n${ds.map(showDeps).mkString("\n")}\n")
      // println(s"zs backtrack:\n${(zs.take(9) ++ zs.takeRight(2)).map(backtrack2(gatesMap)).mkString("\n")}\n")

      println(s"part 1: ${solution1(input)}")
      println(
        "gates sorted by zs:\n\n" + sortGates(
          input.gates.map {
            _.swapOut(Aux("fph"), Vec("z", 15))
              .swapOut(Aux("gds"), Vec("z", 21))
              .swapOut(Aux("wrk"), Aux("jrs"))
              .swapOut(Aux("cqk"), Vec("z", 34))
          },
          zs
        )
          .map { batch =>
            val wire = batch._1
            val gates = batch._2.map("\t" + _.fold(identity, _.toString)).mkString("\n")
            s"$wire:\n$gates"
          }
          // .take(5)
          .mkString("\n\n")
      )
      val swappedWires = Seq("fph", "z15", "gds", "z21", "wrk", "jrs", "cqk", "z34")
      println(s"part 2: ${swappedWires.sorted.mkString(",")}")
    }.get
  }

  case class Input(wires: Map[Wire, Boolean], gates: List[Gate])

  def gatesOutputs(gates: List[Gate]): Map[Wire, Gate] = {
    gates.iterator.map { gate => gate.out -> gate }.toMap
  }

  case class Gate(op: Op, inA: Wire, inB: Wire, out: Wire) {
    override def toString: String = s"$inA $op $inB -> $out"

    def wires: Seq[Wire] = Seq(inA, inB, out)

    private def inputsInOrder: Boolean = (inA, inB) match
      case (Aux(a), Aux(b)) => a <= b
      case (a: Vec, b: Vec) => a.n > b.n || a.name <= b.name
      case (_: Vec, _: Aux) => true
      case _                => false

    def sortInputs: Gate = if inputsInOrder then this else copy(inA = inB, inB = inA)

    def rename(renames: Map[Wire, Wire]): Gate = copy(
      inA = renames.getOrElse(inA, inA),
      inB = renames.getOrElse(inB, inB),
      out = renames.getOrElse(out, out)
    )

    def matches(ta: String, top: Op, tb: String, numP: (Int, Int) => Boolean): Boolean = this match
      case Gate(_, Vec(a, na), Vec(b, nb), _) => a == ta && op == top && b == tb && numP(na, nb)
      case _                                  => false

    def swapOut(o1: Wire, o2: Wire): Gate =
      if out == o1 then copy(out = o2)
      else if out == o2 then copy(out = o1)
      else this
  }

  def replaceStr(from: String, to: String)(s: String): String = if s == from then to else s

  private val wireRe = raw"([a-z]+)(\d*)".r
  def parseWire(wire: String): Wire = wire match {
    case wireRe(name, n) => if n.isEmpty then Aux(name) else Vec(name, n.toInt)
  }

  sealed trait Op {
    def eval(a: Boolean, b: Boolean): Boolean
  }

  object Op {
    case object And extends Op:
      def eval(a: Boolean, b: Boolean): Boolean = a && b
      override def toString: String = "AND"

    case object Or extends Op:
      def eval(a: Boolean, b: Boolean): Boolean = a || b
      override def toString: String = "OR"

    case object Xor extends Op:
      def eval(a: Boolean, b: Boolean): Boolean = a ^ b
      override def toString: String = "XOR"

    def fromString(s: String): Op = s match
      case "AND" => Op.And
      case "OR"  => Op.Or
      case "XOR" => Op.Xor
  }

  def parseInput(lines: IterableOnce[String]): Input = {
    val (wireLines, gateLines) = lines.iterator.dropWhile(_.isEmpty).span(_.nonEmpty)
    Input(
      wires = wireLines.map { line =>
        line.split(":\\s+") match
          case Array(wire, state) => parseWire(wire) -> toBool(state)
          case _                  => throw new Exception(s"unexpected wire line: $line")
      }.toMap,
      gates = gateLines
        .filterNot(_.isBlank)
        .map { line =>
          line.split(' ') match
            case Array(a, op, b, "->", res) => Gate(Op.fromString(op), parseWire(a), parseWire(b), parseWire(res))
            case _                          => throw new Exception(s"unexpected gate line: $line")
        }
        .toList
    )
  }

  def toBool(s: String): Boolean = s match
    case "0" => false
    case "1" => true
    case _   => throw new Exception(s"unexpected wire state: $s")

  // part 1
  def solution1(input: Input): BigInt = {
    val wires: Map[Wire, Boolean] = simulate(input)
    val bits = selectVecBits(wires)("z")
    toNum(bits)
  }

  def selectVecBits(wires: Map[Wire, Boolean])(name: String): Seq[Boolean] =
    wires.iterator
      .collect { case (Vec(wireName, n), state) if wireName == name => (n, state) }
      .toSeq
      .sortBy(_._1)
      .map(_._2)

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

  def simulate(input: Input): Map[Wire, Boolean] = {
    @tailrec
    def go(
        wires: Map[Wire, Boolean],
        changed: Boolean,
        gates1: List[Gate],
        gates2: List[Gate]
    ): Map[Wire, Boolean] = gates1 match {
      case Nil => if changed && gates2.nonEmpty then go(wires, false, gates2, Nil) else wires
      case gate :: gates1 =>
        (for {
          a <- wires.get(gate.inA)
          b <- wires.get(gate.inB)
        } yield gate.out -> gate.op.eval(a, b)) match {
          case None                => go(wires, changed, gates1, gate :: gates2)
          case Some(wire -> state) =>
            // if wire.startsWith("z") then println(s"update $wire")
            go(wires.updated(wire, state), true, gates1, gates2)
        }
    }
    go(input.wires, false, input.gates, Nil)
  }

  // part 2
  def backtrack(gatesMap: Map[Wire, Gate])(wire: Wire): String = {
    def go(wire: Wire): String = {
      gatesMap.get(wire) match
        case None       => wire.toString
        case Some(gate) => s"$wire = (${go(gate.inA)}) ${gate.op} (${go(gate.inB)})"
    }
    go(wire)
  }

  def backtrack2(gatesMap: Map[Wire, Gate])(wire: Wire): String = {
    def go(wire: Wire): (String, Set[Wire]) = {
      gatesMap.get(wire) match
        case None => (wire.toString, Set(wire))
        case Some(gate) =>
          val (resA, inputsA) = go(gate.inA)
          val (resB, inputsB) = go(gate.inB)
          (s"($resA ${gate.op} $resB)", inputsA ++ inputsB)
    }
    val (res, inputs) = go(wire)
    s"$wire (${listWires(inputs)}) = $res"
  }

  private def showDeps(wire: String, ds: Set[Wire]) = s"$wire(${listWires(ds)})"

  def deps(gatesMap: Map[Wire, Gate])(wire: Wire): Set[Wire] = {
    def go(wire: Wire): Set[Wire] = {
      gatesMap.get(wire) match
        case None       => Set(wire)
        case Some(gate) => go(gate.inA) ++ go(gate.inB)
    }
    go(wire)
  }

  def listWires(wires: Set[Wire]): String = {
    val aux: Set[Aux] = selectAux(wires)
    val vg: Seq[String] = selectVec(wires).view
      .mapValues(ws => joinRanges(ws.map(_.n)))
      .toSeq
      .sortBy(_._1)
      .flatMap { (name, ns) =>
        ns.map {
          case Left(num)         => s"$name$num"
          case Right((from, to)) => s"$name$from..$to"
        }
      }
    (vg ++ aux).mkString(", ")
  }

  def joinRanges(ns: Iterable[Int]): List[Either[Int, (Int, Int)]] =
    ns.toVector.sorted.foldLeft[List[Either[Int, (Int, Int)]]](Nil) { (acc, num) =>
      acc match
        case Nil                                        => Left(num) :: acc
        case Left(from) :: acc1 if from + 1 == num      => Right(from -> num) :: acc1
        case Right((from, to)) :: acc1 if to + 1 == num => Right(from -> num) :: acc1
        case _                                          => Left(num) :: acc
    }

  def sortGates(gates: List[Gate], zs: Iterable[Wire]): Iterable[(Wire, List[Either[Wire, Gate]])] = {
    val gatesMap: Map[Wire, Gate] = renameWires(gates.map(_.sortInputs)).map { gate => gate.out -> gate }.toMap
    val visited = mutable.Set[Wire]()
    @tailrec
    def go(wires: Queue[Wire], acc: List[Either[Wire, Gate]]): List[Either[Wire, Gate]] =
      wires.dequeueOption match {
        case None => acc
        case Some((wire, wires)) =>
          if visited.contains(wire) then go(wires, acc)
          else {
            visited += wire
            gatesMap.get(wire) match
              case None       => go(wires, Left(wire) :: acc)
              case Some(gate) => go(wires.enqueueAll(List(gate.inA, gate.inB).sorted.reverse), Right(gate) :: acc)
          }
      }
    zs.map(wire => wire -> go(Queue(wire), Nil)) ++
      (gatesMap.keySet -- visited).toSeq.sorted.map { wire =>
        wire -> List(Right(gatesMap(wire)))
      }
  }

  def renameWires(gates: List[Gate]): List[Gate] = {
    def rename(name: String)(p: Gate => Boolean)(gates: List[Gate]): List[Gate] = {
      val renames: Map[Wire, Wire] = gates.collect {
        case g @ Gate(_, Vec(_, na), _, out: Aux) if p(g) => out -> Vec(name, na)
      }.toMap
      gates.map(_.rename(renames).sortInputs)
    }
    (
      rename("sum")(_.matches("x", Op.Xor, "y", _ == _)) andThen
        rename("carry")(_.matches("x", Op.And, "y", _ == _)) andThen
        rename("sum_prev_n_carry")(_.matches("sum", Op.Xor, "carry", _ == _ + 1)) andThen
        rename("carry2")(_.matches("sum", Op.And, "carry", _ == _ + 1)) andThen
        Function.chain(
          List.fill(43)(
            rename("carry3")(_.matches("carry", Op.Or, "carry2", _ == _)) andThen
              rename("carry2")(_.matches("sum", Op.And, "carry3", _ == _ + 1))
          )
        )
    )(gates)
  }
}
