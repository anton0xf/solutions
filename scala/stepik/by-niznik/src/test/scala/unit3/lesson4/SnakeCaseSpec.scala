package unit3.lesson4

import munit.FunSuite

class SnakeCaseSpec extends FunSuite {
  test("samples") {
    assertEquals(SnakeCase.check("A"), false)
    assertEquals(SnakeCase.check("B"), false)
    assertEquals(SnakeCase.check("Z"), false)
    assertEquals(SnakeCase.check("a"), true)
    assertEquals(SnakeCase.check("abc_defg_xyz"), true)
    assertEquals(SnakeCase.check("aB"), false)
    assertEquals(SnakeCase.check("a1"), false)
    assertEquals(SnakeCase.check("a-"), false)
    assertEquals(SnakeCase.check("a!"), false)
    assertEquals(SnakeCase.check("a_"), false)
    assertEquals(SnakeCase.check("_a"), false)
    assertEquals(SnakeCase.check("a_b"), true)
    assertEquals(SnakeCase.check("a_bc"), true)
    assertEquals(SnakeCase.check("ab_c"), true)
    assertEquals(SnakeCase.check("ab__c"), false)
    assertEquals(SnakeCase.check("ab___c"), false)
    assertEquals(SnakeCase.check("ab_c_d"), true)
    assertEquals(SnakeCase.check("ab_c_de"), true)
    assertEquals(SnakeCase.check("a_b_ccc_d_e"), true)
  }
}
