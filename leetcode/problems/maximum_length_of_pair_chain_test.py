from problems.maximum_length_of_pair_chain import search_l, Solution


def test_search_l():
    assert search_l([[1, 2], [2, 3], [3, 4]], 0) == 0
    assert search_l([[1, 2], [2, 3], [3, 4]], 1) == 1
    assert search_l([[1, 2], [2, 3], [3, 4]], 2) == 2
    assert search_l([[1, 2], [2, 3], [3, 4]], 3) == 3
    assert search_l([[1, 2], [2, 3], [3, 4]], 4) == 3


def test():
    s = Solution()
    assert s.findLongestChain([[1, 2], [2, 3], [3, 4]]) == 2
    assert s.findLongestChain([[1, 2], [7, 8], [4, 5]]) == 3
    assert s.findLongestChain([[1, 4], [1, 2], [7, 8], [4, 5]]) == 3
    assert s.findLongestChain([[1, 2], [3, 7], [4, 5], [6, 7]]) == 3
    assert s.findLongestChain(
        [[2, 5], [-8, 4], [2, 4], [5, 8], [8, 9], [8, 9],
         [7, 9], [-1, 5], [6, 10]]
    ) == 2
