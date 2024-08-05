package arith

import Token.*
import arith.Lexer.tokenize

class LexerTest extends munit.FunSuite:
  test("tokenize constants"):
    assertEquals(tokenize("true false\n0"), List(True, False, Zero))
    assertEquals(
      tokenize(" ( 0 0)   false  "),
      List(OpenBracket, Zero, Zero, CloseBracket, False)
    )

  test("tokenize functions"):
    assertEquals(tokenize("succ(0)"), List(Succ, OpenBracket, Zero, CloseBracket))
    assertEquals(tokenize("pred(succ 0)"), List(Pred, OpenBracket, Succ, Zero, CloseBracket))

  test("tokenize if"):
    assertEquals(tokenize("if true then succ(0) else false"),
      List(If, True, Then, Succ, OpenBracket, Zero, CloseBracket, Else, False))