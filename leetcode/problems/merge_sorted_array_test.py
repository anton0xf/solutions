from problems.merge_sorted_array import Solution

s = Solution()


def test1():
    nums1 = [1, 2, 3, 0, 0, 0]
    s.merge(nums1, 3, [2, 5, 6], 3)
    assert nums1 == [1, 2, 2, 3, 5, 6]


def test2():
    nums1 = [1]
    s.merge(nums1, 1, [], 0)
    assert nums1 == [1]


def test3():
    nums1 = [0]
    s.merge(nums1, 0, [1], 1)
    assert nums1 == [1]


def test4():
    nums1 = [3, 4, 0, 0]
    s.merge(nums1, 2, [1, 2], 2)
    assert nums1 == [1, 2, 3, 4]
