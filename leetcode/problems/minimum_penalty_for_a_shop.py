# https://leetcode.com/problems/minimum-penalty-for-a-shop/

class Solution:
    def bestClosingTime(self, customers: str) -> int:
        n = len(customers)
        vs = [int(ch == 'Y') for ch in customers]
        p = sum(vs)
        min_p = p
        min_i = 0
        for i in range(1, n+1):
            p += 1 - 2*vs[i-1]
            if p < min_p:
                min_p = p
                min_i = i
        return min_i
