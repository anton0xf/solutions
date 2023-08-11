def toList(x):
    if x == 0:
        yield 0
        return
    while x != 0:
        yield x % 10
        x //= 10


class Solution:

    def isPalindrome(self, x: int) -> bool:
        if x < 0:
            return False
        xs = list(toList(x))
        n = len(xs)
        for i in range(n // 2):
            if xs[i] != xs[n - 1 - i]:
                return False
        return True
