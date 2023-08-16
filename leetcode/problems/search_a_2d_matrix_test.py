from problems.search_a_2d_matrix import Solution

s = Solution()


def test():
    assert s.searchMatrix([[1, 3, 5, 7],
                           [10, 11, 16, 20],
                           [23, 30, 34, 60]],
                          3)
    assert not s.searchMatrix([[1, 3, 5, 7],
                               [10, 11, 16, 20],
                               [23, 30, 34, 60]],
                              13)
