# https://leetcode.com/problems/maximum-length-of-pair-chain/
from typing import List


def search_l(pairs: List[List[int]], target_l: int) -> int:
    """get minimum i so that pairs[i][0] > target_l"""
    f, t = 0, len(pairs)
    while f < t:
        i = (f + t) // 2
        val = pairs[i][0]
        if val <= target_l:
            f = i + 1
        else:
            t = i
    return t


class Solution:
    def findLongestChain(self, pairs: List[List[int]]) -> int:
        """
        l[i], r[i] = pairs[i]

        G = (V, E)
        V = set(pairs)
        E = {(i,j): r[i] < l[j]

        L = max(L[i] for i in range(n))
        = max(L[i] for i: l[i] <= min_r)

        min_r = min(r[j] for j in range(n))

        L[i] = 1 + max(L[j] for j: r[i] < l[j])
        """
        pairs.sort(key=lambda p: p[0])
        n = len(pairs)
        min_r = min((r for _, r in pairs))
        roots = (i for i, p in enumerate(pairs) if p[0] <= min_r)
        l_cache = [None] * n

        def L(i):
            if l_cache[i]:
                return l_cache[i]
            l, r = pairs[i]
            k = search_l(pairs, r)
            res = 1 + max((L(j) for j in range(k, n)), default=0)
            l_cache[i] = res
            return res

        return max((L(i) for i in roots), default=0)
