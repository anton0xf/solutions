from typing import List


def count_digits(n):
    if n == 0:
        return 1
    count = 0
    while n != 0:
        n //= 10
        count += 1
    return count


class Solution:
    def findNumbers(self, nums: List[int]) -> int:
        return sum(count_digits(n) % 2 == 0 for n in nums)
