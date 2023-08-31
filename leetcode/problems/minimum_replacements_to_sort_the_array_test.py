from problems.minimum_replacements_to_sort_the_array import Solution


def test():
    s = Solution()
    assert s.minimumReplacement([3, 9, 3]) == 2
    assert s.minimumReplacement([1, 2, 3, 4, 5]) == 0
    assert s.minimumReplacement([12, 9, 7, 6, 17, 19, 21]) == 6
