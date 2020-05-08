from typing import List


class Solution:
    def findMaxConsecutiveOnes(self, nums: List[int]) -> int:
        max_cons = cur_cons = 0
        for n in nums:
            if n == 1:
                cur_cons += 1
                max_cons = max(max_cons, cur_cons)
            else:
                assert n == 0
                cur_cons = 0
        return max_cons
