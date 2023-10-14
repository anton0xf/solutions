# https://leetcode.com/problems/jump-game
from typing import List


class Solution:
    def canJump(self, nums: List[int]) -> bool:
        n = len(nums)
        if n < 2:
            return True
        m = [None] * n

        def dfs(i):
            if m[i] is not None:
                return m[i]
            res = False
            jump = nums[i]
            if jump == 0:
                res = False
            elif i + jump >= n-1:
                res = True
            else:
                for j in range(jump, 0, -1):
                    if dfs(i+j):
                        res = True
                        break
            m[i] = res
            return res

        return dfs(0)
