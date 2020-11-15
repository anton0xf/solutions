import number_of_students_doing_homework_at_a_given_time as sol

s = sol.Solution()


def test_ex1():
    assert 1 == s.busyStudent([1, 2, 3], [3, 2, 7], 4)


def test_ex2():
    assert 1 == s.busyStudent([4], [4], 4)


def test_ex3():
    assert 0 == s.busyStudent([4], [4], 5)


def test_ex4():
    assert 0 == s.busyStudent([1, 1, 1, 1], [1, 3, 2, 4], 7)


def test_ex5():
    assert 5 == s.busyStudent([9, 8, 7, 6, 5, 4, 3, 2, 1],
                              [10, 10, 10, 10, 10, 10, 10, 10, 10],
                              5)
