# https://leetcode.com/problems/two-sum/
from typing import List


class Solution:
    def twoSum(self, nums: List[int], target: int) -> List[int]:
        m = {}  # value -> index in nums
        for i, x in enumerate(nums):
            m[x] = i
        for i, x in enumerate(nums):
            t = target - x
            if t in m and i != m[t]:
                return [i, m[t]]
