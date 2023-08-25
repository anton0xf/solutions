# https://leetcode.com/problems/valid-anagram/
from collections import defaultdict
from typing import Dict


def count_chars(s: str) -> Dict[str, int]:
    res = defaultdict(int)
    for ch in s:
        res[ch] += 1
    return res


class Solution:
    def isAnagram(self, s: str, t: str) -> bool:
        return count_chars(s) == count_chars(t)
