package arith

import arith.Token.*

enum Term:
  case True, False, Zero
  case If(cond: Term, thenBr: Term, elseBr: Term)
  case Succ(x: Term)
  case Pred(x: Term)
  case IsZero(x: Term)

case class ParseState[A](runSt: List[Token] => (A, List[Token])) {
  def flatMap[B](f: A => ParseState[B]): ParseState[B] = ParseState { (tokens: List[Token]) =>
    val (x, rest1) = runSt(tokens)
    f(x).runSt(rest1)
  }

  def map[B](f: A => B): ParseState[B] = flatMap((x: A) => ParseState { (f(x), _) })

  def <*[B](st: ParseState[B]): ParseState[A] = for {
    x <- this
    _ <- st
  } yield x
}

object Parser {
  def parse(tokens: List[Token]): Term =
    val (term, rest) = parseExpr.runSt(tokens)
    if rest.nonEmpty
    then throw new RuntimeException(s"Unexpected token ${rest.head}. Expected end of input")
    else term

  def toTokens(ast: Term): List[Token] = ???

  def skip(token: Token): ParseState[Unit] = ParseState {
    case Nil           => throw new RuntimeException(s"Unexpected end of input. Expected $token")
    case token :: rest => ((), rest)
  }

  def parseExpr: ParseState[Term] = ParseState {
    case Nil                 => throw new RuntimeException("Unexpected end of input")
    case True :: rest        => (Term.True, rest)
    case False :: rest       => (Term.False, rest)
    case Zero :: rest        => (Term.Zero, rest)
    case OpenBracket :: rest => (parseExpr <* skip(CloseBracket)).runSt(rest)
    case CloseBracket :: _   => throw new RuntimeException("Unexpected close bracket")
    case Succ :: rest        => parseExpr.map(Term.Succ(_)).runSt(rest)
    case Pred :: rest        => parseExpr.map(Term.Pred(_)).runSt(rest)
    case IsZero :: rest      => parseExpr.map(Term.IsZero(_)).runSt(rest)
    case If :: rest          => parseIf.runSt(rest)
    case Else :: _           => throw new RuntimeException("Unexpected 'else'")
    case Then :: _           => throw new RuntimeException("Unexpected 'then'")
  }

  def parseIf: ParseState[Term] =
    for {
      condT <- parseExpr <* skip(Then)
      thenT <- parseExpr <* skip(Else)
      elseT <- parseExpr
    } yield Term.If(condT, thenT, elseT)
}
