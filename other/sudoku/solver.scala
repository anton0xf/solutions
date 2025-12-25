package sudoku

import sudoku.impl.Board

@main
def main(): Unit = {
  println(Board.readFrom(io.Source.stdin).map(_.solve()))
}
