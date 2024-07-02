from typing import List


class Solution:
    def removeElement(self, xs: List[int], val: int) -> int:
        # first val index
        j = next((i for i, x in enumerate(xs) if x == val), None)
        if j is None:
            return len(xs)
        i = j + 1
        while i < len(xs):
            if xs[i] != val:
                xs[j] = xs[i]
                j += 1
            i += 1
        return j
