from typing import List


class Solution:
    def duplicateZeros(self, xs: List[int]) -> None:
        i = j = 0
        for x in xs:
            j += 2 if x == 0 else 1
            if j >= len(xs):
                break
            i += 1
        j -= 1
        if j == len(xs):
            if xs[i] == 0:
                xs[j-1] = 0
                j -= 2
            else:
                j -= 1
            i -= 1
        while i >= 0:
            if xs[i] == 0:
                xs[j] = xs[j-1] = 0
                j -= 2
            else:
                xs[j] = xs[i]
                j -= 1
            i -= 1
