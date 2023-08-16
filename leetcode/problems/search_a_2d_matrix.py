# https://leetcode.com/problems/search-a-2d-matrix/
from typing import List


class Solution:
    def searchMatrix(self, matrix: List[List[int]], target: int) -> bool:
        m = len(matrix)  # rows count
        n = len(matrix[0])  # cols count
        N = m * n

        def get(i):
            return matrix[i // n][i % n]

        f = 0
        t = N
        while f < t:
            c = (f + t) // 2
            x = get(c)
            if x == target:
                return True
            if x > target:
                t = c
            else:
                assert x < target
                f = c + 1

        return False
