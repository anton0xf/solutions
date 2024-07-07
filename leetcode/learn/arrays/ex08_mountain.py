# Valid Mountain Array
# https://leetcode.com/explore/learn/card/fun-with-arrays/527/searching-for-items-in-an-array/3251/
from typing import List


class Solution:
    def validMountainArray(self, xs: List[int]) -> bool:
        if len(xs) < 3 or xs[0] >= xs[1]:
            return False
        f = False  # was the top reached
        i = 2
        while i < len(xs):
            if xs[i-1] == xs[i]:
                return False
            if xs[i-1] < xs[i]:
                if f:
                    return False
            elif not f:
                f = True
            i += 1
        return f
