//> using target.scope test
import Day03.*

class Day03Test extends munit.FunSuite {
  test("re1.matches") {
    assertEquals(re1.matches("mul(1,2)"), true)
    assertEquals(re1.matches("mul( 1,2)"), false)
    assertEquals(re1.matches("mul(,2)"), false)
    assertEquals(re1.matches("mul(1,22)"), true)
    assertEquals(re1.matches("mul(123,222)"), true)
    assertEquals(re1.matches("mul(1,1234)"), false)
    assertEquals(re1.matches("mul(1,123 )"), false)
    assertEquals(re1.matches("mul(1,123 "), false)
  }
  test("re1.findPrefixMatchOf") {
    val mOpt = re1.findPrefixMatchOf("mul(1,23)")
    assert(mOpt.isDefined)
    val m = mOpt.get
    assertEquals(m.groupCount, 2)
    assertEquals(m.group(1), "1")
    assertEquals(m.group(2), "23")
  }
  test("re1.findFirstIn") {
    val mOpt = re1.findFirstMatchIn("asdf*mul mul(1,23)")
    assert(mOpt.isDefined)
    val m = mOpt.get
    assertEquals(m.groupCount, 2)
    assertEquals(m.group(1), "1")
    assertEquals(m.group(2), "23")
  }
  test("re1.findAllMatchIn") {
    val ms = re1.findAllMatchIn("asdf*mul mul(1,23)mul(12,3456)mul(333,21)")

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
  test("solution1") {
    val input = "xmul(2,4)%&mul[3,7]!@^do_not_mul(5,5)+mul(32,64]then(mul(11,8)mul(8,5))"
    assertEquals(solution1(input), BigInt(161))
  }
  // part 2
  test("re2.matches") {
    assertEquals(re2.matches("mul(1,2)"), true)
    assertEquals(re2.matches("mul( 1,2)"), false)
    assertEquals(re2.matches("mul(,2)"), false)
    assertEquals(re2.matches("mul(1,22)"), true)
    assertEquals(re2.matches("mul(123,222)"), true)
    assertEquals(re2.matches("mul(1,1234)"), false)
    assertEquals(re2.matches("mul(1,123 )"), false)
    assertEquals(re2.matches("mul(1,123 "), false)
    assertEquals(re2.matches("do()"), true)
    assertEquals(re2.matches("do"), false)
    assertEquals(re2.matches("do(1,2)"), false)
    assertEquals(re2.matches("don't()"), true)
  }
  test("re2.findPrefixMatchOf mul") {
    val mOpt = re2.findPrefixMatchOf("mul(1,23)")
    assert(mOpt.isDefined)
    val m = mOpt.get
    assertEquals(m.groupCount, 5)
    assertEquals(m.group(1), null)
    assertEquals(m.group(2), null)
    assertEquals(m.group(3), "mul")
    assertEquals(m.group(4), "1")
    assertEquals(m.group(5), "23")
  }
  test("re2.findPrefixMatchOf do") {
    val mOpt = re2.findPrefixMatchOf("do()")
    assert(mOpt.isDefined)
    val m = mOpt.get
    assertEquals(m.groupCount, 5)
    assertEquals(m.group(1), "do")
    assertEquals(m.group(2), null)
    assertEquals(m.group(3), null)
    assertEquals(m.group(4), null)
    assertEquals(m.group(5), null)
  }
  test("re2.findPrefixMatchOf don't") {
    val mOpt = re2.findPrefixMatchOf("don't()")
    assert(mOpt.isDefined)
    val m = mOpt.get
    assertEquals(m.groupCount, 5)
    assertEquals(m.group(1), null)
    assertEquals(m.group(2), "don't")
    assertEquals(m.group(3), null)
    assertEquals(m.group(4), null)
    assertEquals(m.group(5), null)
  }
  test("solution2") {
    val input = "xmul(2,4)&mul[3,7]!^don't()_mul(5,5)+mul(32,64](mul(11,8)undo()?mul(8,5))"
    assertEquals(solution2(input), BigInt(48))
  }
}
