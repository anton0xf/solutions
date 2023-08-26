# https://leetcode.com/problems/longest-common-prefix/
from typing import List


class Solution:
    def longestCommonPrefix(self, strs: List[str]) -> str:
        if len(strs) == 1:
            return strs[0]
        strs.sort()
        s1, s2 = strs[0], strs[-1]
        res = ""
        for i in range(min(len(s1), len(s2))):
            if s1[i] == s2[i]:
                res += s1[i]
            else:
                break
        return res
