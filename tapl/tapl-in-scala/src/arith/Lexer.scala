package arith

import scala.util.matching.Regex

enum Token:
  case True, False, If, Then, Else, Zero, Succ, Pred, IsZero
  case OpenBracket, CloseBracket

object Lexer {
  import arith.Token.*
  private val strToTokens: Map[String, Token] = Map(
    "true" -> True,
    "false" -> False,
    "if" -> If,
    "then" -> Then,
    "else" -> Else,
    "0" -> Zero,
    "succ" -> Succ,
    "pred" -> Pred,
    "iszero" -> IsZero,
    "(" -> OpenBracket,
    ")" -> CloseBracket
  )

  private val tokensToStr: Map[Token, String] = strToTokens.map(_.swap)

  def tokenize(program: String): List[Token] = program
    .split("\\b\\s*")
    .toList
    .map(_.trim)
    .filter(_.nonEmpty)
    .map(s => strToTokens.getOrElse(s, throw new RuntimeException(s"Unexpected token '$s'")))
  def tokenToStr(token: Token): String = ???
}
