import problems.three_sum as sol

s = sol.Solution()


def test():
    assert set(s.threeSum([-1, 0, 1, 2, -1, -4])) == {(-1, -1, 2), (-1, 0, 1)}
    assert set(s.threeSum([0, 1, 1])) == set()
    assert set(s.threeSum([0, 0, 0])) == {(0, 0, 0)}
    assert set(s.threeSum([-2, 0, 1, 1, 2])) == {(-2, 0, 2), (-2, 1, 1)}
