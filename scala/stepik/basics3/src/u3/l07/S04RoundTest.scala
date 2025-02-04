//> using target.scope test
package u3.l07

import munit.*
import S04Round.*
import scala.math.*

class S04RoundTest extends FunSuite {
  def checkRoundX(x: Double): Unit = assertEquals(roundX(x), round(x), s"round($x)")

  test("roundX examples") {
    checkRoundX(1)
    checkRoundX(1.1)
    checkRoundX(1.5)
    checkRoundX(0)
    checkRoundX(-1)
    checkRoundX(-1.5)
    checkRoundX(-1.6)
  }

  test("roundX -5..5") {
    (-50 to 50).map(_ / 10.0).map(checkRoundX)
  }
}
