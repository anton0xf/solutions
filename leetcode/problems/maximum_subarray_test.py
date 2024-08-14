from problems.maximum_subarray import Solution

s = Solution()


def test():
    assert 6 == s.maxSubArray([1, 2, 3])
    assert -1 == s.maxSubArray([-2, -1])
    assert 6 == s.maxSubArray([1, 2, -1, -2, 2, 1, -2, 1, 4, -5, 4])
