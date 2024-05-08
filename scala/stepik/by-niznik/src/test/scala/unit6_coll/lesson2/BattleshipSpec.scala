package unit6_coll.lesson2

import munit.FunSuite

class BattleshipSpec extends FunSuite {
  import Naval._
  import Battleship._

  val smallField: Field = Vector.fill(2)(Vector.fill(2)(false))
  val smallGame: Game = (smallField, Map())

  test("putToField") {
    assertEquals(
      putToField(smallField, (0, 0)),
      Vector(Vector(true, false), Vector(false, false))
    )
    assertEquals(
      putToField(smallField, (0, 1)),
      Vector(Vector(false, true), Vector(false, false))
    )
    // put again
    assertEquals(
      putToField(Vector(Vector(false, true), Vector(false, false)), (0, 1)),
      Vector(Vector(false, true), Vector(false, false))
    )
    assertEquals(
      putToField(smallField, (1, 0)),
      Vector(Vector(false, false), Vector(true, false))
    )
    assertEquals(
      putToField(smallField, (1, 1)),
      Vector(Vector(false, false), Vector(false, true))
    )
    assertEquals(
      putToField(Vector(Vector(false, true), Vector(false, false)), (1, 1)),
      Vector(Vector(false, true), Vector(false, true))
    )
  }

  test("tryAddShip one free") {
    assertEquals(
      tryAddShip(smallGame, "test", List((0, 1))),
      (
        Vector(Vector(false, true), Vector(false, false)),
        Map("test" -> List((0, 1)))
      )
    )
  }

  test("tryAddShip one occupied") {
    val game: Game = (Vector(Vector(false, true), Vector(false, false)), Map())
    assertEquals(tryAddShip(game, "test", List((0, 1))), game)
  }

  // TODO tryAddShip two horizontal (x = const) free
  // TODO tryAddShip two horizontal (x = const) occupied
  // TODO tryAddShip two vertical (y = const) free
  // TODO tryAddShip two diagonal
  // TODO tryAddShip two horizontal with gap
  // TODO tryAddShip two vertical with gap

  test("add fleet 1") {
    val fleet: Fleet = Map(
      "MillenniumFalcon" -> List((2, 5), (3, 5), (4, 5), (5, 5)),
      "Varyag" -> List((9, 9))
    )
    assertEquals(
      tryAddFleet(initGame, fleet)._2.keySet,
      Set("MillenniumFalcon", "Varyag")
    )
  }

  test("add fleet 2") {
    val fleet: Fleet = Map(
      "BlackPearl" -> List((1, 6), (1, 7), (1, 8)),
      "MillenniumFalcon" -> List((2, 5), (3, 5), (4, 5), (5, 5)),
      "Varyag" -> List((9, 9))
    )
    assertEquals(
      tryAddFleet(initGame, fleet)._2.keySet,
      Set("BlackPearl", "Varyag")
    )
  }
}
