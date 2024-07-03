import learn.arrays.ex06_remove_duplicates as sol

s = sol.Solution()


def test1():
    xs = [1, 2, 2, 3]
    k = s.removeDuplicates(xs)
    assert 3 == k
    assert [1, 2, 3] == xs[:k]


def test_ex1():
    xs = [1, 1, 2]
    k = s.removeDuplicates(xs)
    assert 2 == k
    assert [1, 2] == xs[:k]


def test_ex2():
    xs = [0, 0, 1, 1, 1, 2, 2, 3, 3, 4]
    k = s.removeDuplicates(xs)
    assert 5 == k
    assert [0, 1, 2, 3, 4] == xs[:k]
