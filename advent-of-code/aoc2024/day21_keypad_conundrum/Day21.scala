import scala.annotation.{tailrec, targetName}
import scala.collection.{immutable, mutable}
import scala.util.Using
import scala.io.Source

object Day21 {
  def main(args: Array[String]): Unit = {
    Using(Source.fromFile("day21_keypad_conundrum/input")) { source =>
      val input = parseInput(source.getLines())
      println(s"part 1: ${solution1(input)}")
      println(s"part 2: ${solution2(input)}")
    }
  }

  type Input = List[String]

  def parseInput(lines: IterableOnce[String]): Input = lines.iterator.toList

  case class Vec(i: Int, j: Int) {
    @targetName("plus")
    def +(p: Vec): Vec = Vec(i + p.i, j + p.j)

    @targetName("minus")
    def -(p: Vec): Vec = Vec(i - p.i, j - p.j)
  }

  val numpad: Pad = Pad(
    """789
      |456
      |123
      |.0A""".stripMargin
  )

  val dirpad: Pad = Pad(
    """.^A
      |<v>""".stripMargin
  )

  val dirs: Map[Char, Vec] = Map(
    '^' -> Vec(-1, 0),
    'v' -> Vec(1, 0),
    '<' -> Vec(0, -1),
    '>' -> Vec(0, 1)
  )

  case class Pad(pad: Vector[Vector[Char]]) {
    val find: Map[Char, Vec] = (for {
      (row, i) <- pad.iterator.zipWithIndex
      (ch, j) <- row.zipWithIndex
    } yield ch -> Vec(i, j)).toMap

    val start: Vec = find('A')
    def get(p: Vec): Option[Char] = pad.lift(p.i).flatMap(_.lift(p.j)).filterNot(_ == '.')
  }

  object Pad {
    def apply(s: String): Pad = Pad(s.split('\n').map(_.toVector).toVector)
  }

  def simulate(program: String, pad: Pad): Option[String] = {
    def go(cmds: List[Char], pos: Vec, out: Vector[Char]): Option[String] = cmds match
      case Nil => Some(out.mkString)
      case cmd :: cmds =>
        cmd match
          case 'A' => pad.get(pos).flatMap { ch => go(cmds, pos, out :+ ch) }
          case dir =>
            val pos1 = pos + dirs(dir)
            if pad.get(pos1).isDefined then go(cmds, pos1, out) else None

    go(program.toList, pad.start, Vector())
  }

  // part 1
  def solution1(input: Input): Int = {
    input.map(complexity).sum
  }

  def complexity(s: String): Int = {
    val length = typeIndirect(s).head.length
    val num = s.replace("A", "").toInt
    length * num
  }

  def typeIndirect(s: String): LazyList[String] = {
    val progs1 = typeString(s, numpad)
    val progs2 = typeShortest(progs1, dirpad)
    typeShortest(progs2, dirpad)
  }

  def typeShortest(progs: LazyList[String], pad: Pad): LazyList[String] = {
    val ps = progs.map(typeString(_, dirpad))
    val shortestSize = ps.map(_.head.length).min
    ps.filter(_.head.length == shortestSize).flatten
  }

  def typeString(s: String, pad: Pad): LazyList[String] = {
    @tailrec
    def go(s: List[Char], p: Vec, acc: LazyList[Vector[Char]]): LazyList[String] = s match
      case Nil => acc.map(_.mkString)
      case ch :: s =>
        val progs = typeCharM(ch, p, pad)
        go(s, pad.find(ch), acc.flatMap(pre => progs.map(pre ++ _)))

    go(s.toList, pad.start, LazyList(Vector()))
  }

  val typeCharCache: mutable.Map[(Char, Vec, Pad), List[Vector[Char]]] = mutable.Map()

  def typeCharM(ch: Char, p: Vec, pad: Pad): List[Vector[Char]] =
    typeCharCache.getOrElseUpdate((ch, p, pad), typeChar(ch, p, pad))

  def typeChar(ch: Char, p: Vec, pad: Pad): List[Vector[Char]] = {
    def moveJ(dj: Int) = Vector.fill(dj.abs)(if dj >= 0 then '>' else '<')
    def moveI(di: Int) = Vector.fill(di.abs)(if di >= 0 then 'v' else '^')
    val q = pad.find(ch)
    (q - p match
      case Vec(0, dj) => List(moveJ(dj))
      case Vec(di, 0) => List(moveI(di))
      case Vec(di, dj) =>
        (if pad.get(p + Vec(di, 0)).isDefined then List(moveI(di) ++ moveJ(dj)) else Nil) ++
          (if pad.get(p + Vec(0, dj)).isDefined then List(moveJ(dj) ++ moveI(di)) else Nil)
    ).map(_ :+ 'A')
  }

  // part 2
  def solution2(input: Input): BigInt = {
    input.map(complexity2(numpad :: List.fill(25)(dirpad))).sum
  }

  def complexity2(pads: List[Pad])(s: String): BigInt = {
    val length = typeStringIndirect(pads, s)
    val num = s.replace("A", "").toInt
    length * num
  }

  def typeIndirect2(n: Int, s: String): Int = {
    val progs = typeString(s, numpad)
    @tailrec
    def go(n: Int, progs: LazyList[String]): LazyList[String] =
      if n == 0 then progs else go(n - 1, typeShortest(progs, dirpad))
    go(n, progs).head.length
  }

  def typeStringIndirect(pads: List[Pad], s: String): BigInt = {
    // println(s"type $s at level ${pads.size}")
    @tailrec
    def go(s: List[Char], p: Vec, acc: BigInt): BigInt = s match
      case Nil     => acc
      case ch :: s => go(s, pads.head.find(ch), acc + typeCharIndirectM(ch, p, pads))

    go(s.toList, pads.head.start, 0)
  }

  val typeCharIndirectCache: mutable.Map[(Char, Vec, Int), BigInt] = mutable.Map()

  def typeCharIndirectM(ch: Char, p: Vec, pads: List[Pad]): BigInt =
    typeCharIndirectCache.getOrElseUpdate((ch, p, pads.size), typeCharIndirect(ch, p, pads))

  def typeCharIndirect(ch: Char, p: Vec, pads: List[Pad]): BigInt = {
    // println(s"type '$ch' from $p at level ${pads.size}")
    pads match
      case Nil         => 1
      case pad :: Nil  => typeCharM(ch, p, pad).map(_.size).min
      case pad :: pads => typeCharM(ch, p, pad).map(chs => typeStringIndirect(pads, chs.mkString)).min
  }
}
