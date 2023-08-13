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
            if i > 0 and ni == nums[i-1]:
                continue
            j = i + 1
            k = n - 1
            while j < k:
                nj = nums[j]
                nk = nums[k]
                s1 = ni + nj
                if s1 > 0 or nk < 0:
                    break
                s = s1 + nk
                if s == 0:
                    res.add((ni, nj, nk))
                    while j < k-1 and nj == nums[j+1]:
                        j += 1
                    j += 1
                    while j < k-1 and nk == nums[k-1]:
                        k -= 1
                    k -= 1
                elif s < 0:
                    while j < k-1 and nj == nums[j+1]:
                        j += 1
                    j += 1
                else:
                    while j < k-1 and nk == nums[k-1]:
                        k -= 1
                    k -= 1
        return res
