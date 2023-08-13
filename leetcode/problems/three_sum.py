# https://leetcode.com/problems/3sum/

from typing import List


class Solution:
    def threeSum(self, nums: List[int]) -> List[List[int]]:
        n = len(nums)
        nums.sort()
        res = set()
        for i in range(n - 2):
            ni = nums[i]
            if ni > 0:
                break
            j = i + 1
            k = n - 1
            while j < k:
                s1 = ni + nums[j]
                if s1 > 0 or nums[k] < 0:
                    break
                s = s1 + nums[k]
                if s == 0:
                    res.add((ni, nums[j], nums[k]))
                    j += 1
                    k -= 1
                elif s < 0:
                    j += 1
                else:
                    k -= 1
        return res
