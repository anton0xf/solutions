# https://leetcode.com/problems/powx-n/


class Solution:
    def myPow(self, x: float, n: int) -> float:
        if n < 0:
            return 1. / self.myPow(x, -n)
        res = 1.
        while n > 0:
            if n % 2 == 0:
                x *= x
                n //= 2
            else:
                res *= x
                n -= 1
        return res
