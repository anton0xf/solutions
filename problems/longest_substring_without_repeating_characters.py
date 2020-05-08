# https://leetcode.com/problems/longest-substring-without-repeating-characters/
class Solution:
    def lengthOfLongestSubstring(self, s: str) -> int:
        i = 0
        longest_len = 0
        chars = set()
        for j, ch in enumerate(s):
            while ch in chars:
                chars.remove(s[i])
                i += 1
            chars.add(ch)
            cur_len = j - i + 1
            if cur_len > longest_len:
                longest_len = cur_len
        return longest_len
