# https://leetcode.com/problems/valid-palindrome/

class Solution:
    def isPalindrome(self, s: str) -> bool:
        chs = [ch for ch in s.lower() if ch.isalnum()]
        n = len(chs)
        h = n // 2
        return chs[:h] == chs[n:n-h-1:-1]
