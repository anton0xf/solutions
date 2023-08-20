# https://leetcode.com/problems/contains-duplicate/
from typing import List


class Solution:
    def containsDuplicate(self, nums: List[int]) -> bool:
        s = set()
        for n in nums:
            if n in s:
                return True
            s.add(n)
        return False

    # sort approach (better memory usage)
    def containsDuplicate2(self, nums: List[int]) -> bool:
        nums.sort()
        prev = None
        for i, n in enumerate(nums):
            if i > 0 and n == prev:
                return True
            prev = n
        return False
