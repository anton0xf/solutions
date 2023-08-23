from problems.remove_duplicates_from_sorted_array import Solution

s = Solution()


def test1():
    arr = [1, 1, 2]
    assert s.removeDuplicates(arr) == 2
    assert arr[:2] == [1, 2]


def test2():
    arr = [0, 0, 1, 1, 1, 2, 2, 3, 3, 4]
    assert s.removeDuplicates(arr) == 5
    assert arr[:5] == [0, 1, 2, 3, 4]
