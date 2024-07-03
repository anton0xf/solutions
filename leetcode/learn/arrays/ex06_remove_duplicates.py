from typing import List


class Solution:

    def removeDuplicates(self, xs: List[int]) -> int:
        j = None
        i = 1
        while i < len(xs):
            if i == 0:
                continue
            if xs[i - 1] == xs[i]:
                if j is None:
                    j = i
            elif j is not None:
                xs[j] = xs[i]
                j += 1
            i += 1
        return j if j is not None else len(xs)
