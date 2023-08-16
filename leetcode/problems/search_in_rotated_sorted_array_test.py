from problems.search_in_rotated_sorted_array import Solution

s = Solution()


def test_search_pivot():
    assert s.search_pivot([2, 0, 1]) == 2
    assert s.search_pivot([4, 0, 1, 2]) == 3
    assert s.search_pivot([4, 5, 6, 7, 0, 1, 2]) == 3
    assert s.search_pivot([1]) == 0


def test_search():
    assert s.search([4, 5, 6, 7, 0, 1, 2], 0) == 4
    assert s.search([4, 5, 6, 7, 0, 1, 2], 3) == -1
    assert s.search([1], 0) == -1
