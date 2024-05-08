package unit6_coll.lesson2
// https://stepik.org/lesson/106520/step/9?unit=81046

import scala.io.StdIn

object Naval {
  type Point = (Int, Int) // (x, y)
  type Field = Vector[Vector[Boolean]]
  type Ship = List[Point]
  type Fleet = Map[String, Ship]
  type Game = (Field, Fleet)
}

object Battleship {
  import Naval._

  def main(args: Array[String]): Unit = {
    val n = StdIn.readInt()
    val fleetIn: Fleet = List.fill(n)(readShip()).toMap
    val game = tryAddFleet(initGame, fleetIn)
    val fleetOut = game._2
    fleetOut.keys.foreach(println)
  }

  val initField: Field = Vector.fill(10)(Vector.fill(10)(false))
  val initGame: Game = (initField, Map())

  def readShip(): (String, Ship) = {
    val Array(name, lenStr) = StdIn.readLine().split(' ')
    val len = lenStr.toInt
    val points = List.fill(len)(readPoint())
    (name, points)
  }

  def readPoint(): Point = StdIn.readLine().split(' ').map(_.toInt) match {
    case Array(x, y) => (x, y)
  }

  def tryAddFleet(game: Game, fleet: Fleet): Game = {
    fleet.foldLeft(game)((game, ship) => tryAddShip(game, ship._1, ship._2))
  }

  def tryAddShip(game: Game, name: String, ship: Ship): Game = {
    val (field: Field, fleet: Fleet) = game
    val newField: Field = ship.foldLeft(field)(putToField)
    val newFleet: Fleet = fleet.updated(name, ship)
    (newField, newFleet)
  }

  def getFromField(field: Field, point: Point): Boolean =
    field(point._1)(point._2)

  def putToField(field: Field, point: Point): Field =
    updateInVector(
      field,
      point._1,
      (row: Vector[Boolean]) => row.updated(point._2, true)
    )

  def updateInVector[T](vec: Vector[T], idx: Int, f: T => T): Vector[T] =
    vec.updated(idx, f(vec(idx)))

  /** определить, подходит ли корабль по своим характеристикам */
  def validateShip(ship: Ship): Boolean = ???

  /** определить, можно ли его поставить */
  def validatePosition(ship: Ship, field: Field): Boolean = ???

  /** добавить корабль во флот */
  def enrichFleet(fleet: Fleet, name: String, ship: Ship): Fleet = ???

  /** пометить клетки, которые занимает добавляемый корабль */
  def markUsedCells(field: Field, ship: Ship): Field = ???
}
