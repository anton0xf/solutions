//> using target.scope test
import Day03.*

class Day03Test extends munit.FunSuite {
  test("re.matches") {
    assertEquals(re.matches("mul(1,2)"), true)
    assertEquals(re.matches("mul( 1,2)"), false)
    assertEquals(re.matches("mul(,2)"), false)
    assertEquals(re.matches("mul(1,22)"), true)
    assertEquals(re.matches("mul(123,222)"), true)
    assertEquals(re.matches("mul(1,1234)"), false)
    assertEquals(re.matches("mul(1,123 )"), false)
    assertEquals(re.matches("mul(1,123 "), false)
  }
  test("re.findPrefixMatchOf") {
    val mOpt = re.findPrefixMatchOf("mul(1,23)")
    assert(mOpt.isDefined)
    val m = mOpt.get
    assertEquals(m.groupCount, 2)
    assertEquals(m.group(1), "1")
    assertEquals(m.group(2), "23")
  }
  test("re.findFirstIn") {
    val mOpt = re.findFirstMatchIn("asdf*mul mul(1,23)")
    assert(mOpt.isDefined)
    val m = mOpt.get
    assertEquals(m.groupCount, 2)
    assertEquals(m.group(1), "1")
    assertEquals(m.group(2), "23")
  }
  test("re.findAllMatchIn") {
    val ms = re.findAllMatchIn("asdf*mul mul(1,23)mul(12,3456)mul(333,21)")

    assert(ms.hasNext)
    val m1 = ms.next()
    assertEquals(m1.groupCount, 2)
    assertEquals(m1.group(1), "1")
    assertEquals(m1.group(2), "23")

    assert(ms.hasNext)
    val m2 = ms.next()
    assertEquals(m2.groupCount, 2)
    assertEquals(m2.group(1), "333")
    assertEquals(m2.group(2), "21")

    assert(!ms.hasNext)
  }
}
