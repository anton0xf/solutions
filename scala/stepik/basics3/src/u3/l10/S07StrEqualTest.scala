//> using target.scope test
package u3.l10

import munit.*
import S07StrEqual.*

class S07StrEqualTest extends FunSuite {
  test("areEqual") {
    assert(areEqual("abc", "abc"))
    assert(!areEqual("ab", "abc"))
    assert(!areEqual("abc", "a"))
    assert(!areEqual("", "abc"))
    assert(!areEqual("", "abc"))
    assert(areEqual("", ""))
  }
}
