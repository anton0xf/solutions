from nose.tools import eq_
import problems._002_add_two_numbers as sol


def linked(*xs):
    return sol.to_linked(xs)


def to_list(lst):
    return list(sol.from_linked(lst))


def test_reverse():
    lst = linked(*range(5))
    expected = list(reversed(range(5)))
    eq_(expected, to_list(sol.reverse(lst)))


# 342 + 465 = 807
def test_from_task():
    l1 = linked(2, 4, 3)
    l2 = linked(5, 6, 4)
    expected = [7, 0, 8]
    s = sol.Solution()
    eq_(expected, to_list(s.addTwoNumbers(l1, l2)))


# 942 + 465 = 1407
def test_last_carry():
    l1 = linked(2, 4, 9)
    l2 = linked(5, 6, 4)
    expected = [7, 0, 4, 1]
    s = sol.Solution()
    eq_(expected, to_list(s.addTwoNumbers(l1, l2)))
