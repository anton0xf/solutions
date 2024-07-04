from typing import List


class Solution:
    def checkIfExist(self, xs: List[int]) -> bool:
        vals = set()
        for i, x in enumerate(xs):
            if x * 2 in vals or (x % 2 == 0 and x // 2 in vals):
                return True
            vals.add(x)
        return False
