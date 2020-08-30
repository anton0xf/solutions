import learn.arrays.ex02_even_number_of_digits as sol

s = sol.Solution()


def test_count_digits():
    assert 1 == sol.count_digits(0)
    assert 1 == sol.count_digits(3)
    assert 2 == sol.count_digits(20)
    assert 2 == sol.count_digits(83)
    assert 3 == sol.count_digits(201)
    assert 3 == sol.count_digits(210)


def test_example1():
    assert 2 == s.findNumbers([12, 345, 2, 6, 7896])


def test_example2():
    assert 1 == s.findNumbers([555, 901, 482, 1771])
