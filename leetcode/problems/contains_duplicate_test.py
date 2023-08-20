from problems.contains_duplicate import Solution

s = Solution()


def test():
    assert s.containsDuplicate([1, 2, 3, 1])
    assert not s.containsDuplicate([1, 2, 3, 4])
    assert s.containsDuplicate([1, 1, 1, 3, 3, 4, 3, 2, 4, 2])
