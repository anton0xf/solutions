import learn.arrays.ex05_deleting_items_from_an_array as sol

s = sol.Solution()


def test_example():
    xs = [3, 2, 2, 3]
    k = s.removeElement(xs, 3)
    assert 2 == k
    assert [2, 2] == xs[:k]


def test1():
    xs = [1, 2]
    k = s.removeElement(xs, 1)
    assert 1 == k
    assert [2] == xs[:k]


def test2():
    xs = [2, 2, 3]
    k = s.removeElement(xs, 3)
    assert 2 == k
    assert [2, 2] == xs[:k]


def test3():
    xs = [3, 3, 2, 2, 3]
    k = s.removeElement(xs, 3)
    assert 2 == k
    assert [2, 2] == xs[:k]
