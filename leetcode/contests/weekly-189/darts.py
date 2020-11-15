from typing import List
from math import sqrt


def distance(x, y):
    return sqrt(x**2 + y**2)


def in_dartboard(p, r):
    x, y = p
    return distance(x, y) <= r


class Solution:
    def numPoints(self, points: List[List[int]], r: int) -> int:
        return sum(in_dartboard(p, r) for p in points)
