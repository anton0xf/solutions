# https://leetcode.com/problems/search-a-2d-matrix/
from typing import List


class Solution:
    def searchMatrix(self, matrix: List[List[int]], target: int) -> bool:
        m = len(matrix)  # rows count
        n = len(matrix[0])  # cols count
        f = 0
        t = m * n
        while f < t:
            c = (f + t) // 2
            x = matrix[c // n][c % n]
            if x == target:
                return True
            if x > target:
                t = c
            else:
                assert x < target
                f = c + 1
        return False
