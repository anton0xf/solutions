from problems.reverse_integer import Solution

s = Solution()


def test():
    assert s.reverse(123) == 321
    assert s.reverse(-123) == -321
    assert s.reverse(120) == 21
    assert s.reverse(-2**31) == 0
    assert s.reverse(2**31 - 1) == 0
