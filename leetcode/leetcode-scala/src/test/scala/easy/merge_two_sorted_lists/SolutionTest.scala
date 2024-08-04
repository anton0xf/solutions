package easy.merge_two_sorted_lists

import munit.FunSuite

class SolutionTest extends FunSuite {
  test("Example 1") {
    val list1 = ListNode(1, 2, 4)
    val list2 = ListNode(1, 3, 4)
    val expected = ListNode(1, 1, 2, 3, 4, 4)
    assertEquals(Solution.mergeTwoLists(list1, list2), expected)
  }

  test("Example 2") {
    val nil = ListNode()
    assertEquals(Solution.mergeTwoLists(nil, nil), nil)
  }

  test("Example 3") {
    test("Example 2") {
      assertEquals(Solution.mergeTwoLists(ListNode(), ListNode(0)), ListNode(0))
    }
  }
}
