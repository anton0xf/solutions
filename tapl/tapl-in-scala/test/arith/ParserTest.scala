package arith

import arith.Token.*

class ParserTest extends munit.FunSuite:
  test("parse constants"):
    assertEquals(Parser.parse(List(True)), Term.True)
    assertEquals(Parser.parse(List(False)), Term.False)
    assertEquals(Parser.parse(List(Zero)), Term.Zero)

  test("parse constant in brackets"):
    assertEquals(Parser.parse(List(OpenBracket, True, CloseBracket)), Term.True)
    assertEquals(Parser.parse(List(OpenBracket, OpenBracket, False, CloseBracket, CloseBracket)), Term.False)
    intercept[RuntimeException] { Parser.parse(List(OpenBracket, True)) }
    intercept[RuntimeException] { Parser.parse(List(OpenBracket, CloseBracket)) }
    intercept[RuntimeException] { Parser.parse(List(False, CloseBracket)) }
    intercept[RuntimeException] { Parser.parse(List(CloseBracket)) }
    intercept[RuntimeException] {Parser.parse(List(OpenBracket, CloseBracket, True))}

  test("parse fun"):
    assertEquals(Parser.parse(List(Succ, Zero)), Term.Succ(Term.Zero))
    assertEquals(Parser.parse(List(Pred, OpenBracket, Zero, CloseBracket)), Term.Pred(Term.Zero))
    assertEquals(Parser.parse(List(OpenBracket, IsZero, Zero, CloseBracket)), Term.IsZero(Term.Zero))
    assertEquals(Parser.parse(List(Pred, Succ, Zero)), Term.Pred(Term.Succ(Term.Zero)))
    intercept[RuntimeException] { Parser.parse(List(Succ)) }
    intercept[RuntimeException] { Parser.parse(List(Succ, CloseBracket)) }
    intercept[RuntimeException] { Parser.parse(List(Succ, OpenBracket, Zero)) }

  test("parse if"):
    assertEquals(Parser.parse(List(If, True, Then, Zero, Else, Succ, Zero)),
      Term.If(Term.True, Term.Zero, Term.Succ(Term.Zero)))
    assertEquals(Parser.parse(List(If, If, True, Then, False, Else, True, Then, Zero, Else, Succ, Zero)),
      Term.If(Term.If(Term.True, Term.False, Term.True), Term.Zero, Term.Succ(Term.Zero)))
    intercept[RuntimeException] { Parser.parse(List(If, True, Then, Zero, Else, Succ)) }
    intercept[RuntimeException] { Parser.parse(List(If, True, Then, Zero, Else)) }
    intercept[RuntimeException] { Parser.parse(List(If, True, Then, Zero)) }
    intercept[RuntimeException] { Parser.parse(List(If, True, Then)) }
    intercept[RuntimeException] { Parser.parse(List(If, True)) }
    intercept[RuntimeException] { Parser.parse(List(If)) }
    intercept[RuntimeException] { Parser.parse(List(Then)) }
    intercept[RuntimeException] { Parser.parse(List(Else)) }