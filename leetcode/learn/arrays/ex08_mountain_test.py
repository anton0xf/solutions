from learn.arrays.ex08_mountain import Solution

s = Solution()


def test_small():
    assert not s.validMountainArray([])
    assert not s.validMountainArray([1])
    assert not s.validMountainArray([1, 2])


def test_ex1():
    xs = [2, 1]
    assert not s.validMountainArray(xs)


def test_no_dec():
    xs = [1, 2, 3]
    assert not s.validMountainArray(xs)


def test_ex2():
    xs = [3, 5, 5]
    assert not s.validMountainArray(xs)


def test_ex3():
    xs = [0, 3, 2, 1]
    assert s.validMountainArray(xs)
