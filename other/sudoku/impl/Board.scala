package sudoku.impl

import scala.io.Source

case class Pos(i: Byte, j: Byte) {
  import Board.squareSize
  private def sameRow(p: Pos): Boolean = i == p.i
  private def sameCol(p: Pos): Boolean = j == p.j
  private def sameSquare(p: Pos): Boolean =
    (i / squareSize == p.i / squareSize) &&
      (j / squareSize == p.j / squareSize)
  def same(p: Pos): Boolean = sameRow(p) || sameCol(p) || sameSquare(p)
}

object Pos {
  def apply(i: Int, j: Int): Pos = Pos(i.toByte, j.toByte)
}

type Val = Byte

final case class Board(m: Map[Pos, Set[Val]]) {
  def set(pos: Pos, d: Val): Option[Board] = {
    val board = Board(m.map { case (p, vals) =>
      p -> (if p == pos then Set(d)
            else if p.same(pos) then vals - d
            else vals)
    })
    Some(board).filter(_.valid)
  }

  private def valid: Boolean = {
    m.forall {
      case (pos, vals) => vals.size match {
          case 0 => false
          case 1 =>
            val d = vals.head
            !m.iterator.exists((p, vs) => pos != p && pos.same(p) && (vs - d).isEmpty)
          case _ => true
        }
    }
  }

  override def toString: String =
    (0 until Board.size).map { i =>
      (0 until Board.size).map(j => Board.fmtVals(m(Pos(i, j)))).mkString(", ")
    }.mkString("\n")

  private enum SimplestUnsolved:
    case Inconsistent // there are some cells without vals
    case Solved // all cells have one val
    case Some(pos: Pos, vals: Set[Val])

  private def simplestUnsolved: SimplestUnsolved = {
    import SimplestUnsolved.*
    m.foldLeft(Solved) {
      case (Inconsistent, _) => Inconsistent
      case (res, cur @ pos -> vals) =>
        vals.size match {
          case 0 => Inconsistent
          case 1 => res
          case n => res match {
              case Solved => Some(pos, vals)
              case Some(_, minVals) => if n < minVals.size then Some(pos, vals) else res
              case _ => throw new RuntimeException(s"unexpected res: $res")
            }
        }
    }
  }

  def solve(): Option[Board] = {
    simplestUnsolved match {
      case SimplestUnsolved.Inconsistent => None
      case SimplestUnsolved.Solved => Some(this)
      case SimplestUnsolved.Some(p, vals) if vals.size < 2 =>
        throw new RuntimeException(s"$p vals ($vals) should contain at least two vals")
      case SimplestUnsolved.Some(p, vals) =>
        vals.flatMap(d => set(p, d).flatMap(_.solve())).headOption // ??
      case x => throw new RuntimeException(s"unexpected simplestUnsolved: $x")
    }
  }
}

object Board {
  val squareSize = 3
  val size = squareSize * squareSize
  val allVals: Set[Val] = (1 to size).map(_.toByte).toSet
  val allPos: Seq[Pos] = for { i <- 0 until size; j <- 0 until size } yield Pos(i, j)

  val empty: Board = Board(allPos.map(_ -> allVals).toMap)

  private def from(vals: Iterator[(Pos, Val)]): Option[Board] = {
    vals.foldLeft[Option[Board]](Some(empty)) {
      case (None, _) => None
      case (Some(board), (pos, d)) => board.set(pos, d)
    }
  }

  def readFrom(source: Source): Option[Board] = {
    from(for {
      (ln, i) <- source.getLines().filterNot(_.isBlank).zipWithIndex
      (s, j) <- ln.split(',').zipWithIndex
      d <- s.trim.toByteOption
      if d > 0
    } yield Pos(i, j) -> d)
  }

  def fmtVals(vals: Set[Val]): String = {
    vals.toSeq.sorted match {
      case Seq() => "_"
      case Seq(d) => d.toString
      case vals if vals.size <= 3 => vals.mkString("{", "", "}")
      case vals => val str = vals.take(3).mkString(""); s"{$str..}"
    }
  }
}
