# https://leetcode.com/problems/valid-anagram/
from typing import Dict


def count_chars(s: str) -> Dict[str, int]:
    res = {}
    for ch in s:
        res[ch] = res.get(ch, 0) + 1
    return res


class Solution:
    def isAnagram(self, s: str, t: str) -> bool:
        return count_chars(s) == count_chars(t)
