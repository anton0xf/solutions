import learn.arrays.ex03_squares_of_a_sorted_array as sol

s = sol.Solution()


def test_example1():
    assert [0, 1, 9, 16, 100] == s.sortedSquares([-4, -1, 0, 3, 10])


def test_example2():
    assert [4, 9, 9, 49, 121] == s.sortedSquares([-7, -3, 2, 3, 11])
