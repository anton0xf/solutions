# https://leetcode.com/problems/binary-search/

from typing import List


class Solution:
    def search(self, nums: List[int], target: int) -> int:
        f = 0
        t = len(nums)
        while f < t:
            i = (f + t) // 2
            print(f, i, t)
            if nums[i] == target:
                return i
            if nums[i] < target:
                f = i + 1
            else:
                t = i
        return -1
