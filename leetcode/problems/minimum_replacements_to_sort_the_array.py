# https://leetcode.com/problems/minimum-replacements-to-sort-the-array/
from typing import List


class Solution:
    def minimumReplacement(self, nums: List[int]) -> int:
        n = len(nums)
        if n < 2:
            return 0
        res = 0
        m = nums[-1]
        for i in range(n - 2, -1, -1):
            x = nums[i]
            if x <= m:
                m = x
            else:
                steps = (x - 1) // m
                res += steps
                m = x // (steps + 1)
        return res
