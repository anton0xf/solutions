package arith

import Token.*

class LexerTest extends munit.FunSuite:
  test("tokenize constants"):
    assertEquals(Lexer.tokenize("true false\n0"), List(True, False, Zero))
    assertEquals(
      Lexer.tokenize(" ( 0 0)   false  "),
      List(OpenBracket, Zero, Zero, CloseBracket, False)
    )

  test("tokenize functions"):
    assertEquals(Lexer.tokenize("succ(0)"), List(Succ, OpenBracket, Zero, CloseBracket))
    assertEquals(Lexer.tokenize("pred(succ 0)"), List(Pred, OpenBracket, Succ, Zero, CloseBracket))

  test("tokenize if"):
    assertEquals(Lexer.tokenize("if true then succ(0) else false"),
      List(If, True, Then, Succ, OpenBracket, Zero, CloseBracket, Else, False))