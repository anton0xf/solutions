package arith

import Token.*

class LexerTest extends munit.FunSuite:
  test("tokenize constants"):
    assertEquals(Lexer.tokenize("true false\n0"), List(True, False, Zero))
