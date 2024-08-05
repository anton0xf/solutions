package arith

import arith.Token.*

enum Term:
  case True, False, Zero
  case If(cond: Term, thenBr: Term, elseBr: Term)
  case Succ(x: Term)
  case Pred(x: Term)
  case IsZero(x: Term)

type ParseState = (Option[Term], List[Token])

object ParseState {
  def apply(term: Term, rest: List[Token]): ParseState = (Some(term), rest)
  def none(rest: List[Token]): ParseState = (None, rest)
}

object Parser {
  def parse(tokens: List[Token]): Term =
    val (res, rest) = parseExpr(tokens)
    if rest.nonEmpty
    then throw new RuntimeException(s"Unexpected token ${rest.head}. Expected end of input")
    else
      res match
        case None       => throw new RuntimeException(s"Cannot parse $tokens")
        case Some(term) => term

  def toTokens(ast: Term): List[Token] = ???

  def thenIgnore(state: ParseState, token: Token): ParseState = state match
    case (_, Nil) => throw new RuntimeException(s"Unexpected end of input. Expected $token")
    case (x, token :: rest) => (x, rest)

  def thenMap(state: ParseState, f: Term => Term): ParseState = (state._1.map(f), state._2)

  def parseExpr(tokens: List[Token]): ParseState = tokens match
    case Nil => ParseState.none(tokens) // TODO just throw exception?
    case True :: rest        => ParseState(Term.True, rest)
    case False :: rest       => ParseState(Term.False, rest)
    case Zero :: rest        => ParseState(Term.Zero, rest)
    case OpenBracket :: rest => thenIgnore(parseExpr(rest), CloseBracket)
    case CloseBracket :: _ => throw new RuntimeException("Unexpected close bracket")
    case Succ :: rest => thenMap(parseExpr(rest), Term.Succ(_))
    case Pred :: rest => thenMap(parseExpr(rest), Term.Pred(_))
    case IsZero :: rest => thenMap(parseExpr(rest), Term.IsZero(_))
    case If :: rest => parseIf(rest)
    case Else :: _ => throw new RuntimeException("Unexpected 'else'")
    case Then :: _ => throw new RuntimeException("Unexpected 'then'")

  def parseIf(tokens: List[Token]): ParseState = {
    val (condT, rest1) = thenIgnore(parseExpr(tokens), Then)
    if(condT.isEmpty) throw new RuntimeException("Unexpected end of input")
    val (thenT, rest2) = thenIgnore(parseExpr(rest1), Else)
    if(thenT.isEmpty) throw new RuntimeException("Unexpected end of input")
    val (elseT, rest3) = parseExpr(rest2)
    if(elseT.isEmpty) throw new RuntimeException("Unexpected end of input")
    (Some(Term.If(condT.get, thenT.get, elseT.get)), rest3)
  }
}
