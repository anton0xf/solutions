# https://leetcode.com/problems/search-in-rotated-sorted-array/
from typing import List


class Solution:
    def search_pivot(self, nums: List[int]) -> int:
        n = len(nums)
        if n < 2 or nums[0] < nums[-1]:
            return 0
        f = 0
        t = n - 1
        while t - f > 1:
            assert nums[f] > nums[t]
            c = (f + t) // 2
            if nums[c] > nums[f]:
                f = c
            else:
                assert nums[c] < nums[t]
                t = c
        return n - t

    def search(self, nums: List[int], target: int) -> int:
        n = len(nums)
        k = self.search_pivot(nums)
        f = 0
        t = n
        while f < t:
            c = (f + t) // 2
            # orig[i] = nums[(i + n - k) % n] = nums[(i - k) % n]
            rc = (c - k) % n
            if nums[rc] == target:
                return rc
            elif nums[rc] > target:
                t = c
            else:
                f = c + 1
        return -1
