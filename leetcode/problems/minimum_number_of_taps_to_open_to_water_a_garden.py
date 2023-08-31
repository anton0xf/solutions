# https://leetcode.com/problems/minimum-number-of-taps-to-open-to-water-a-garden/
from typing import List


def argmax(xs, f):
    mfx = mi = mx = None
    for i, x in enumerate(xs):
        fx = f(x)
        if not mfx or fx > mfx:
            mfx = fx
            mi = i
            mx = x
    return mi, mx


class Solution:
    def minTaps(self, n: int, ranges: List[int]) -> int:
        garden = [False] * n  # garden[i] == is_watered([i, i+1])

        def new_watered(i: int, r: int) -> List[int]:
            return [j for j in range(max(0, i-r), min(n, i+r))
                    if not garden[j]]

        rs = list(filter(lambda e: e[1] > 0, enumerate(ranges)))
        rs.sort(key=lambda e: e[1], reverse=True)
        res = 0
        while rs and not all(garden):
            j, w = argmax((new_watered(i, r) for i, r in rs), len)
            for i in w:
                garden[i] = True
            print('i: %d, r: %d, w: %s' % (rs[j][0], rs[j][1], w))
            rs.pop(j)
            res += 1
        return res if all(garden) else -1
