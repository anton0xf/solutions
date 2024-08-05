package arith

import arith.Token.*

import scala.annotation.targetName

enum Term:
  case True, False, Zero
  case If(cond: Term, thenBr: Term, elseBr: Term)
  case Succ(x: Term)
  case Pred(x: Term)
  case IsZero(x: Term)

// TODO use State from Cats
case class ParseState[A](runSt: List[Token] => (A, List[Token])) {
  def flatMap[B](f: A => ParseState[B]): ParseState[B] = ParseState { (tokens: List[Token]) =>
    val (x, rest1) = runSt(tokens)
    f(x).runSt(rest1)
  }

  def map[B](f: A => B): ParseState[B] = flatMap((x: A) => ParseState { (f(x), _) })

  @targetName("productL")
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

  def parseExpr: ParseState[Term] = ParseState {
    case Nil => throw new RuntimeException("Unexpected end of input")
    case term :: rest =>
      (term match {
        case True         => pure(Term.True)
        case False        => pure(Term.False)
        case Zero         => pure(Term.Zero)
        case OpenBracket  => (parseExpr <* skip(CloseBracket))
        case CloseBracket => throw new RuntimeException("Unexpected close bracket")
        case Succ         => parseExpr.map(Term.Succ(_))
        case Pred         => parseExpr.map(Term.Pred(_))
        case IsZero       => parseExpr.map(Term.IsZero(_))
        case If           => parseIf
        case Else         => throw new RuntimeException("Unexpected 'else'")
        case Then         => throw new RuntimeException("Unexpected 'then'")
      }).runSt(rest)
  }

  def skip(token: Token): ParseState[Unit] = ParseState {
    case Nil           => throw new RuntimeException(s"Unexpected end of input. Expected $token")
    case token :: rest => ((), rest)
  }

  def pure[A](x: A): ParseState[A] = ParseState { tokens => (x, tokens) }

  def parseIf: ParseState[Term] =
    for {
      condT <- parseExpr <* skip(Then)
      thenT <- parseExpr <* skip(Else)
      elseT <- parseExpr
    } yield Term.If(condT, thenT, elseT)
}
