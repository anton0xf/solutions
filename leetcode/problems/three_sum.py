# https://leetcode.com/problems/3sum/

from typing import List


class Solution:
    def threeSum(self, nums: List[int]) -> List[List[int]]:
        n = len(nums)
        nums.sort()
        idxs = {n: i for i, n in enumerate(nums)}
        res = []
        for i in range(n - 2):
            ni = nums[i]
            if ni > 0:
                break
            if i > 0 and ni == nums[i-1]:
                continue
            for j in range(i+1, n-1):
                nj = nums[j]
                if j > i+1 and nj == nums[j-1]:
                    continue
                s = ni + nj
                if s > 0:
                    break
                t = -s
                if t in idxs and idxs[t] > j:
                    res.append((ni, nj, t))
        return res
