//> using target.scope test
import Day24.*
import scala.jdk.StreamConverters.*

class Day24Test extends munit.FunSuite {
  import Wire.{Aux, Vec}

  val input0: List[String] =
    """x00: 1
      |y00: 0
      |
      |x00 AND y00 -> z00
      |""".stripMargin.lines().toScala(List)

  val input1: List[String] =
    """x00: 1
      |x01: 1
      |x02: 1
      |y00: 0
      |y01: 1
      |y02: 0
      |
      |x00 AND y00 -> z00
      |x01 XOR y01 -> z01
      |x02 OR y02 -> z02""".stripMargin.lines().toScala(List)

  val input2: List[String] =
    """
      |
      |x00: 1
      |x01: 0
      |x02: 1
      |x03: 1
      |x04: 0
      |y00: 1
      |y01: 1
      |y02: 1
      |y03: 1
      |y04: 1
      |
      |ntg XOR fgs -> mjb
      |y02 OR x01 -> tnw
      |kwq OR kpj -> z05
      |x00 OR x03 -> fst
      |tgd XOR rvg -> z01
      |vdt OR tnw -> bfw
      |bfw AND frj -> z10
      |ffh OR nrd -> bqk
      |y00 AND y03 -> djm
      |y03 OR y00 -> psh
      |bqk OR frj -> z08
      |tnw OR fst -> frj
      |gnj AND tgd -> z11
      |bfw XOR mjb -> z00
      |x03 OR x00 -> vdt
      |gnj AND wpb -> z02
      |x04 AND y00 -> kjc
      |djm OR pbm -> qhw
      |nrd AND vdt -> hwm
      |kjc AND fst -> rvg
      |y04 OR y02 -> fgs
      |y01 AND x02 -> pbm
      |ntg OR kjc -> kwq
      |psh XOR fgs -> tgd
      |qhw XOR tgd -> z09
      |pbm OR djm -> kpj
      |x03 XOR y03 -> ffh
      |x00 XOR y04 -> ntg
      |bfw OR bqk -> z06
      |nrd XOR fgs -> wpb
      |frj XOR qhw -> z04
      |bqk OR frj -> z07
      |y03 OR x01 -> nrd
      |hwm AND bqk -> z03
      |tgd XOR rvg -> z12
      |tnw OR pbm -> gnj
      |""".stripMargin.lines().toScala(List)

  test("parseInput") {
    assertEquals(parseInput(input0), Input(
      Map(Vec("x", 0) -> true, Vec("y", 0) -> false),
      List(Gate(Op.And, Vec("x", 0), Vec("y", 0), Vec("z", 0)))
    ))
  }

  // part 1
  test("solution1"){
    assertEquals(solution1(parseInput(input0)).toInt, 0)
    assertEquals(solution1(parseInput(input1)).toInt, 4)
    assertEquals(solution1(parseInput(input2)).toInt, 2024)
  }


  test("toNum") {
    assertEquals(toNum(Seq(false, true, true)).toInt, 6)
    assertEquals(toNum(Seq(false, true, false, true)).toInt, 10)
    assertEquals(toNum(Seq(false, true, false, true, false)).toInt, 10)
    assertEquals(toNum(Seq(true, false, true, false)).toInt, 5)
  }

  // part 2
}
