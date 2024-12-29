//> using target.scope test
import Day23.*
import scala.jdk.StreamConverters.*

class Day23Test extends munit.FunSuite {
  val input0: List[String] =
    """a-b
      |b-t
      |t-a
      |b-d""".stripMargin.lines().toScala(List)

  val input1: List[String] =
    """kh-tc
      |qp-kh
      |de-cg
      |ka-co
      |yn-aq
      |qp-ub
      |cg-tb
      |vc-aq
      |tb-ka
      |wh-tc
      |yn-cg
      |kh-ub
      |ta-co
      |de-co
      |tc-td
      |tb-wq
      |wh-td
      |ta-ka
      |td-qp
      |aq-cg
      |wq-ub
      |ub-vc
      |de-ta
      |wq-aq
      |wq-vc
      |wh-yn
      |ka-de
      |kh-ta
      |co-tc
      |wh-qp
      |tb-vc
      |td-yn""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input0), List(("a", "b"), ("b", "t"), ("t", "a"), ("b", "d")))
  }

  // part 1
  test("solution1"){
    assertEquals(solution1(parseInput(input0)), 1)
    assertEquals(solution1(parseInput(input1)), 7)
  }

  // part 2
}
