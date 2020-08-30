# https://leetcode.com/problems/add-two-numbers/


# Definition for singly-linked list.
class ListNode:
    def __init__(self, val=0, next=None):
        self.val = val
        self.next = next


def to_linked(xs: list):
    node = None
    for x in reversed(xs):
        node = ListNode(x, node)
    return node


def from_linked(lst: ListNode):
    while lst:
        yield lst.val
        lst = lst.next


class Solution:
    def addTwoNumbers(self, l1: ListNode, l2: ListNode) -> ListNode:
        head_ref = cur = ListNode()
        carry = 0
        while l1 or l2 or carry:
            cur.next = ListNode()
            cur = cur.next
            v1 = l1.val if l1 else 0
            v2 = l2.val if l2 else 0
            val = carry + v1 + v2
            carry, cur.val = divmod(val, 10)
            if l1:
                l1 = l1.next
            if l2:
                l2 = l2.next
        return head_ref.next
