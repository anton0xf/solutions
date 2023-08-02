# https://leetcode.com/problems/two-sum/
from typing import List


class Solution:
    def twoSum(self, nums: List[int], target: int) -> List[int]:
        idxs = {n: i for i, n in enumerate(nums)}
        for i in range(len(nums)):
            comp = target - nums[i]
            if comp in idxs and idxs[comp] != i:
                return [i, idxs[comp]]
