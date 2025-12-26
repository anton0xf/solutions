//> using target.scope test
package sudoku.impl

import munit.*
import sudoku.impl.Board.*

import scala.jdk.StreamConverters.*

class BoardSpec extends FunSuite {
  test("solve sudoku") {
    val in =
      """
        |_, _, _, _, _, _, 9, _, 7
        |_, _, _, 4, 2, _, 1, 8, _
        |_, _, _, 7, _, 5, _, 2, 6
        |1, _, _, 9, _, 4, _, _, _
        |_, 5, _, _, _, _, _, 4, _
        |_, _, _, 5, _, 7, _, _, 9
        |9, 2, _, 1, _, 8, _, _, _
        |_, 3, 4, _, 5, 9, _, _, _
        |5, _, 7, _, _, _, _, _, _
        |""".stripMargin
    val init = readFrom(io.Source.fromString(in))
    val solution = init.flatMap(_.solve())
    assertEquals(
      solution.map(_.toString),
      Some(
        """4, 6, 2, 8, 3, 1, 9, 5, 7
          |7, 9, 5, 4, 2, 6, 1, 8, 3
          |3, 8, 1, 7, 9, 5, 4, 2, 6
          |1, 7, 3, 9, 8, 4, 2, 6, 5
          |6, 5, 9, 3, 1, 2, 7, 4, 8
          |2, 4, 8, 5, 6, 7, 3, 1, 9
          |9, 2, 6, 1, 7, 8, 5, 3, 4
          |8, 3, 4, 2, 5, 9, 6, 7, 1
          |5, 1, 7, 6, 4, 3, 8, 9, 2""".stripMargin
      )
    )
  }

  test("fmtVals") {
    assertEquals(fmtVals(Set()), "_")
    assertEquals(fmtVals(Set(1)), "1")
    assertEquals(fmtVals(Set(1, 2)), "{12}")
    assertEquals(fmtVals(Board.allVals), "{123..}")
  }

  test("set one") {
    val board = empty.set(Pos(0, 0), 7).get
    assertEquals(board.m.get(Pos(0, 0)), Some(Set(7.toByte)))
    assertEquals(board.m.get(Pos(1, 1)), Some(allVals - 7))
    assertEquals(board.m.get(Pos(0, 8)), Some(allVals - 7))
    assertEquals(board.m.get(Pos(8, 0)), Some(allVals - 7))
    assertEquals(board.m.get(Pos(3, 3)), Some(allVals))
    assertEquals(board.m.get(Pos(8, 8)), Some(allVals))
  }

  test("set inconsistent") {
    val board = empty.set(Pos(0, 0), 7)
      .flatMap(_.set(Pos(0, 1), 7))
    assertEquals(board, None)
  }

  test("same") {
    val p = Pos(4, 6)
    val s =
      """
        |_____1___
        |_____1___
        |_____1___
        |_____1___
        |_____1___
        |111111111
        |___111___
        |___111___
        |""".stripMargin
    val res = for {
      (ln, i) <- s.lines().toScala(Iterator).filterNot(_.isBlank).zipWithIndex
      (v, j) <- ln.map(_ == '1').zipWithIndex
    } yield assertEquals(p.same(Pos(i, j)), v)
  }
}
