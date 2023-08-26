# https://leetcode.com/problems/reverse-integer/

class Solution:
    def reverse(self, x: int) -> int:
        res = self._reverse(x) if x >= 0 else -self._reverse(-x)
        return res if res.bit_length() <= 31 else 0

    def _reverse(self, x: int) -> int:
        res = 0
        while x > 0:
            res = res * 10 + x % 10
            x //= 10
        return res
