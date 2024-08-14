# https://leetcode.com/problems/maximum-subarray/
from typing import List


class Solution:
    def maxSubArray(self, xs: List[int]) -> int:
        m = s = None
        for x in xs:
            if s is None:
                s = x
            else:
                s = max(x, s + x)
            if m is None:
                m = s
            else:
                m = max(m, s)
        return m
