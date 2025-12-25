//> using target.scope test
package sudoku.impl

import munit.*
import sudoku.impl.Board.*

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
        """6, 4, 2, 3, 8, 1, 9, 5, 7
        |7, 9, 5, 4, 2, 6, 1, 8, 3
        |3, 8, 1, 7, 9, 5, 4, 2, 6
        |1, 7, 8, 9, 6, 4, 5, 3, 2
        |2, 5, 9, 8, 1, 3, 7, 4, 1
        |4, 6, 3, 5, 1, 7, 8, 1, 9
        |9, 2, 6, 1, 7, 8, 3, 6, 5
        |8, 3, 4, 6, 5, 9, 2, 7, 1
        |5, 1, 7, 6, 3, 2, 6, 9, 4""".stripMargin
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
}
