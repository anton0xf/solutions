package arith

import scala.io.*

@main
def eval(args: String*): Unit = {
  val program = (
    if args.length > 0 then Source.fromFile(args(0)) else Source.stdin
  ).getLines().mkString
  val tokens = Lexer.tokenize(program)
  val ast: Term = Parser.parse(tokens)
  val res: Term = Core.eval(ast)
  val resTokens: List[Token] = Parser.toTokens(ast)
  println(resTokens.map(Lexer.tokenToStr).mkString(" "))
}
