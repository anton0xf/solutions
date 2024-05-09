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

  test("tryAddShip of one free") {
    assertEquals(
      tryAddShip(smallGame, "test", List((0, 1))),
      (
        Vector(Vector(false, true), Vector(false, false)),
        Map("test" -> List((0, 1)))
      )
    )
  }

  test("tryAddShip of one occupied") {
    val game: Game = (Vector(Vector(false, true), Vector(false, false)), Map())
    assertEquals(tryAddShip(game, "test", List((0, 1))), game)
  }

  test("tryAddShip of two horizontal (x = const) free") {
    assertEquals(
      tryAddShip(smallGame, "test", List((0, 1), (0, 0))),
      (
        Vector(Vector(true, true), Vector(false, false)),
        Map("test" -> List((0, 1), (0, 0)))
      )
    )
  }

  test("tryAddShip of two horizontal (x = const) occupied") {
    val game: Game = (Vector(Vector(false, true), Vector(false, false)), Map())
    assertEquals(tryAddShip(game, "test", List((0, 1), (0, 0))), game)
  }

  test("tryAddShip of two vertical (y = const) free") {
    assertEquals(
      tryAddShip(smallGame, "test", List((0, 1), (1, 1))),
      (
        Vector(Vector(false, true), Vector(false, true)),
        Map("test" -> List((0, 1), (1, 1)))
      )
    )
  }

  test("tryAddShip two diagonal") {
    assertEquals(tryAddShip(smallGame, "test", List((0, 0), (1, 1))), smallGame)
  }

  test("tryAddShip of two horizontal with gap") {
    val game: Game = (Vector(Vector(false, false, false)), Map())
    assertEquals(tryAddShip(game, "test", List((0, 0), (0, 2))), game)
  }

  test("tryAddShip of two vertical with gap") {
    val game: Game = (Vector(Vector(false), Vector(false), Vector(false)), Map())
    assertEquals(tryAddShip(game, "test", List((0, 0), (2, 0))), game)
  }

  test("tryAddShip of 4") {
    val game: Game = (Vector(Vector.fill(5)(false)), Map())
    val ship = List((0, 0), (0, 1), (0, 2), (0, 3))
    val newGame: Game = (Vector(Vector(true, true, true, true, false)), Map("test" -> ship))
    assertEquals(tryAddShip(game, "test", ship), newGame)
  }

  test("tryAddShip of more than 4") {
    val game: Game = (Vector(Vector.fill(5)(false)), Map())
    assertEquals(tryAddShip(game, "test", List((0, 0), (0, 1), (0, 2), (0, 3), (0, 4))), game)
  }

  test("tryAddShip out of field") {
    assertEquals(tryAddShip(smallGame, "test", List((0, 2))), smallGame)
  }

  // TODO tryAddShip connected to another

  test("validateHorizontalShip") {
    assertEquals(validateHorizontalShip(List((0, 0), (0, 1))), true)
    assertEquals(validateHorizontalShip(List((5, 0), (5, 1), (5, 3))), false)
    assertEquals(validateHorizontalShip(List((5, 0), (5, 1), (5, 2), (5, 3))), true)
    assertEquals(validateHorizontalShip(List((0, 0), (0, 2))), false)
    assertEquals(validateHorizontalShip(List((0, 0), (0, 1), (0, 2))), true)
    assertEquals(validateHorizontalShip(List((0, 0), (1, 1))), false)
    assertEquals(validateHorizontalShip(List((0, 0), (1, 0))), false)
    assertEquals(validateHorizontalShip(List((0, 0), (1, 0), (3, 0))), false)
    assertEquals(validateHorizontalShip(List((0, 0), (1, 0), (2, 0), (3, 0))), false)
    assertEquals(validateHorizontalShip(List((0, 3), (1, 3), (2, 3), (3, 3))), false)
  }

  test("validateVerticalShip") {
    assertEquals(validateVerticalShip(List((0, 0), (0, 1))), false)
    assertEquals(validateVerticalShip(List((5, 0), (5, 1), (5, 3))), false)
    assertEquals(validateVerticalShip(List((5, 0), (5, 1), (5, 2), (5, 3))), false)
    assertEquals(validateVerticalShip(List((0, 0), (0, 2))), false)
    assertEquals(validateVerticalShip(List((0, 0), (0, 1), (0, 2))), false)
    assertEquals(validateVerticalShip(List((0, 0), (1, 1))), false)
    assertEquals(validateVerticalShip(List((0, 0), (1, 0))), true)
    assertEquals(validateVerticalShip(List((0, 0), (1, 0), (4, 0))), false)
    assertEquals(validateVerticalShip(List((0, 3), (1, 3), (4, 3))), false)
    assertEquals(validateVerticalShip(List((0, 0), (1, 0), (2, 0), (3, 0))), true)
    assertEquals(validateVerticalShip(List((0, 3), (1, 3), (2, 3), (3, 3))), true)
  }

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
