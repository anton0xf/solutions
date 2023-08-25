# https://leetcode.com/problems/longest-common-prefix/
from typing import List


class Solution:
    def longestCommonPrefix(self, strs: List[str]) -> str:
        res = ""
        for n in range(200):
            if n >= len(strs[0]):
                break
            ch = strs[0][n]
            if all((n < len(s) and ch == s[n] for s in strs)):
                res += ch
            else:
                break
        return res
