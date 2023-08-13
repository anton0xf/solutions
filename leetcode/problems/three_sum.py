# https://leetcode.com/problems/3sum/

from typing import List


class Solution:
    def threeSum(self, nums: List[int]) -> List[List[int]]:
        n = len(nums)
        nums.sort()
        print('nums:', nums)
        res = set()
        for i in range(n - 2):
            print('i:', i)
            if nums[i] > 0:
                break
            for j in range(i + 1, n - 1):
                print('j:', j)
                s = nums[i] + nums[j]
                t = -s  # target
                print('target:', t)
                if t < nums[j]:
                    break
                k_min = j + 1
                k_max = n
                while k_min < k_max:
                    k = (k_min + k_max) // 2
                    print('search:', k_min, k, k_max)
                    if nums[k] == t:
                        res.add((nums[i], nums[j], nums[k]))
                        break
                    if nums[k] < t:
                        k_min = k + 1
                    else:
                        k_max = k
        return res
