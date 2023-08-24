# https://leetcode.com/problems/valid-palindrome/

class Solution:
    def isPalindrome(self, s: str) -> bool:
        chs = [ch for ch in s.lower() if ch.isalnum()]
        n = len(chs)
        for i in range(n // 2):
            if chs[i] != chs[-i-1]:
                return False
        return True
