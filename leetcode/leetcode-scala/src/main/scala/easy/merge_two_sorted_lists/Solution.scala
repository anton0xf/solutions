package easy.merge_two_sorted_lists
import scala.annotation.tailrec

// https://leetcode.com/problems/merge-two-sorted-lists/

class ListNode(_x: Int = 0, _next: ListNode = null) {
  var next: ListNode = _next
  var x: Int = _x

  override final def equals(obj: Any): Boolean = (obj != null) && (obj match
    case ref: AnyRef if this eq ref => true
    case node: ListNode => this.x == node.x && this.next == node.next
    case _ => false)
}

object ListNode{
  def apply(xs: Int*): ListNode = ListNode(xs.toList)
  def apply(xs: List[Int]): ListNode = xs match {
    case Nil => null
    case x :: rest => new ListNode(x, ListNode(rest))
  }
}

object Solution {
  def mergeTwoLists(list1: ListNode, list2: ListNode): ListNode = {
    if (list1 == null) list2
    else if (list2 == null) list1
    else {
      if list1.x < list2.x then {
        list1.next = mergeTwoLists(list1.next, list2)
        list1
      } else {
        list2.next = mergeTwoLists(list1, list2.next)
        list2
      }
    }
  }
}
