import learn.arrays.ex04_duplicate_zeros as sol

s = sol.Solution()


def test_one():
    xs = [1]
    s.duplicateZeros(xs)
    assert [1] == xs


def test_one_two_three():
    xs = [1, 2, 3]
    s.duplicateZeros(xs)
    assert [1, 2, 3] == xs


def test_zero():
    xs = [0]
    s.duplicateZeros(xs)
    assert [0] == xs


def test_zero_one():
    xs = [0, 1]
    s.duplicateZeros(xs)
    assert [0, 0] == xs


def test_one_zero():
    xs = [1, 0]
    s.duplicateZeros(xs)
    assert [1, 0] == xs


def test_zero_one_zero():
    xs = [0, 1, 0]
    s.duplicateZeros(xs)
    assert [0, 0, 1] == xs


def test_3_zeros():
    xs = [0, 0, 0]
    s.duplicateZeros(xs)
    assert [0, 0, 0] == xs


def test_complicated():
    xs = [8, 4, 5, 0, 0, 0, 0, 7]
    s.duplicateZeros(xs)
    assert [8, 4, 5, 0, 0, 0, 0, 0] == xs
