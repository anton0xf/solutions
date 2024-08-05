package arith

object Core {
  def eval(ast: Term): Term = ???

  def evalProgram(program: String): String = {
    val tokens = Lexer.tokenize(program)
    val ast: Term = Parser.parse(tokens)
    val res: Term = Core.eval(ast)
    val resTokens: List[Token] = Parser.toTokens(ast)
    resTokens.map(Lexer.tokenToStr).mkString(" ")
  }
}