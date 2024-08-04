package arith

enum Term:
  case True, False, Zero
  case If(cond: Term, thenBr: Term, elseBr: Term)
  case Succ(x: Term)
  case Pred(x: Term)
  case IsZero(x: Term)

object Parser {
  def parse(tokens: List[Token]): Term = ???
  def toTokens(ast: Term): List[Token] = ???
}