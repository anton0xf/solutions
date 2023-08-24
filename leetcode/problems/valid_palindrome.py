# https://leetcode.com/problems/valid-palindrome/

class Solution:
    def isPalindrome(self, s: str) -> bool:
        chs = [ch for ch in s.lower() if ch.isalnum()]
        n = len(chs)
        for i in range(n // 2):
            if chs[i] != chs[-i-1]:
                return False
        return True

    # better memory but worse time
    def isPalindrome2(self, s: str) -> bool:
        i, j = 0, len(s) - 1
        while i < j:
            if not s[i].isalnum():
                i += 1
                continue
            if not s[j].isalnum():
                j -= 1
                continue
            if s[i].lower() != s[j].lower():
                return False
            i += 1
            j -= 1
        return True
