import learn.arrays.ex03_squares_of_a_sorted_array as sol

s = sol.Solution()


def test_example1():
    assert [0, 1, 9, 16, 100] == s.sortedSquares([-4, -1, 0, 3, 10])


def test_example2():
    assert [4, 9, 9, 49, 121] == s.sortedSquares([-7, -3, 2, 3, 11])


def test_non_negative():
    assert [0, 9, 100] == s.sortedSquares([0, 3, 10])


def test_positive():
    assert [9, 100] == s.sortedSquares([3, 10])


def test_non_positive():
    assert [0, 1, 16] == s.sortedSquares([-4, -1, 0])


def test_negative():
    assert [1, 16] == s.sortedSquares([-4, -1])


def test_empty():
    assert [] == s.sortedSquares([])


def test_first_non_negative_index():
    f = sol.first_non_negative_index
    assert f([-1, 0, 1]) == 1
    assert f([0, 1]) == 0
    assert f([1]) == 0
    assert f([-1]) == 1
    assert f([-2, -1]) == 2
    assert f([-2, -1, 0]) == 2
    assert f([-2, -1, 0, 1]) == 2
