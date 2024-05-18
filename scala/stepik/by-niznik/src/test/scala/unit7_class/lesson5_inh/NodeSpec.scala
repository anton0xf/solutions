package unit7_class.lesson5_inh

import munit.FunSuite

class NodeSpec extends FunSuite {
  test("values") {
    val tree = Branch(Leaf(1), Branch(Leaf(2), Leaf(3)))
    assertEquals(tree.values, List(1, 2, 3))
  }

  test("prepend") {
    assertEquals(1 +: Leaf(2), Branch(Leaf(1), Leaf(2)))
    assertEquals(
      1 +: Branch(Leaf(2), Leaf(3)),
      Branch(Branch(Leaf(1), Leaf(2)), Leaf(3))
    )
  }

  test("append") {
    assertEquals(Leaf(1) :+ 2, Branch(Leaf(1), Leaf(2)))
    assertEquals(
      Branch(Leaf(1), Leaf(2)) :+ 3,
      Branch(Leaf(1), Branch(Leaf(2), Leaf(3)))
    )
  }

  test("concat") {
    assertEquals(Leaf(1) ++ Leaf(2), Branch(Leaf(1), Leaf(2)))
    assertEquals(
      Branch(Leaf(1), Leaf(2)) ++ Leaf(3),
      Branch(Branch(Leaf(1), Leaf(2)), Leaf(3))
    )
    assertEquals(
      Leaf(1) ++ Branch(Leaf(2), Leaf(3)),
      Branch(Leaf(1), Branch(Leaf(2), Leaf(3)))
    )
  }
}
