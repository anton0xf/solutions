package arith

import scala.io.*

@main
def eval(args: String*): Unit = {
  val program = (
    if args.nonEmpty then Source.fromFile(args(0)) else Source.stdin
  ).getLines().mkString
  val out: String = Core.evalProgram(program)
  println(out)
}
