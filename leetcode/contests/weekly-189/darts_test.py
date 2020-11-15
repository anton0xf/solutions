import darts as sol

s = sol.Solution()


def check(expected, points, r):
    assert expected == s.numPoints(points, r)


def test_ex():
    check(4, [[-2, 0], [2, 0], [0, 2], [0, -2]], 2)
    check(5, [[-3, 0], [3, 0], [2, 6], [5, 4], [0, 9], [7, 8]], 5)
    check(1, [[-2, 0], [2, 0], [0, 2], [0, -2]], 1)
    check(4, [[1, 2], [3, 5], [1, -1], [2, 3], [4, 1], [1, 3]], 2)
