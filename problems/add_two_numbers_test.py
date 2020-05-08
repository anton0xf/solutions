import problems.add_two_numbers as sol


s = sol.Solution()


def linked(*xs):
    return sol.to_linked(xs)


def to_list(lst):
    return list(sol.from_linked(lst))


# 342 + 465 = 807
def test_from_task():
    l1 = linked(2, 4, 3)
    l2 = linked(5, 6, 4)
    expected = [7, 0, 8]
    assert expected == to_list(s.addTwoNumbers(l1, l2))


# 942 + 465 = 1407
def test_last_carry():
    l1 = linked(2, 4, 9)
    l2 = linked(5, 6, 4)
    expected = [7, 0, 4, 1]
    assert expected == to_list(s.addTwoNumbers(l1, l2))


def test_zero():
    assert [1, 2] == to_list(s.addTwoNumbers(linked(0), linked(1, 2)))


def test_zeros():
    assert [0] == to_list(s.addTwoNumbers(linked(0), linked(0)))
