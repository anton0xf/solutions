from typing import List


def first_non_negative_index(A: List[int]):
    for i, n in enumerate(A):
        if n >= 0:
            return i
    return len(A)


class Solution:
    def sortedSquares(self, A: List[int]) -> List[int]:
        res = []
        i = j = first_non_negative_index(A)
        while j > 0 or i < len(A):
            if j == 0 or (i < len(A) and A[i] < -A[j - 1]):
                res.append(A[i]**2)
                i += 1
            else:
                assert j > 0 and (i == len(A) or A[i] >= -A[j - 1])
                res.append(A[j - 1]**2)
                j -= 1
        return res
