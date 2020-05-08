from typing import List


class Solution:
    def sortedSquares(self, A: List[int]) -> List[int]:
        return sorted([n * n for n in A])
