# https://leetcode.com/problems/reverse-integer/

MIN, MAX = -2**31, 2**31 - 1


class Solution:
    def reverse(self, x: int) -> int:
        if x < 0:
            res = -self._reverse(-x)
            return res if res >= MIN else 0
        else:
            res = self._reverse(x)
            return res if res <= MAX else 0

    def _reverse(self, x: int) -> int:
        res = 0
        while x > 0:
            res = res * 10 + x % 10
            x //= 10
        return res
