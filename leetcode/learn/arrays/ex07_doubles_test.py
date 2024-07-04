from learn.arrays.ex07_doubles import Solution

s = Solution()


def test_ex1():
    xs = [10, 2, 5, 3]
    assert s.checkIfExist(xs)


def test_ex2():
    xs = [3, 1, 7, 11]
    assert not s.checkIfExist(xs)
