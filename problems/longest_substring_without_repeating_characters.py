class Solution:
    def lengthOfLongestSubstring(self, s: str) -> int:
        if not s:
            return 0
        i = 0
        longest_len = 1
        chars = set(s[0])
        for j in range(1, len(s)):
            while s[j] in chars:
                chars.remove(s[i])
                i += 1
            chars.add(s[j])
            cur_len = j - i + 1
            if cur_len > longest_len:
                longest_len = cur_len
        return longest_len
