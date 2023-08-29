# https://leetcode.com/problems/minimum-penalty-for-a-shop/
from operator import add


class Solution:
    def bestClosingTime(self, customers: str) -> int:
        n = len(customers)

        v = [int(ch == 'Y') for ch in customers]
        v.append(0)

        o = [0] * (n+1)
        c = [0] * (n+1)
        acc_o = acc_c = 0
        for i in range(n):
            acc_o += 1 - v[i]
            o[i+1] = acc_o

        for j in range(n, -1, -1):
            acc_c += v[j]
            c[j] += acc_c

        res_v = n
        res_i = 0
        for i, s in enumerate(map(add, o, c)):
            if s < res_v:
                res_v = s
                res_i = i

        return res_i
