# https://leetcode.com/problems/implement-stack-using-queues
from collections import deque


class MyStack:

    def __init__(self):
        self._n = 0
        self._q = deque()

    def push(self, x: int) -> None:
        self._n += 1
        self._q.append(x)

    def pop(self) -> int:
        if self._n < 1:
            return None
        for i in range(self._n - 1):
            t = self._q.popleft()
            self._q.append(t)
        self._n -= 1
        return self._q.popleft()

    def top(self) -> int:
        if self._n < 1:
            return None
        for i in range(self._n - 1):
            t = self._q.popleft()
            self._q.append(t)
        res = self._q.popleft()
        self._q.append(res)
        return res

    def empty(self) -> bool:
        return self._n == 0


# Your MyStack object will be instantiated and called as such:
# obj = MyStack()
# obj.push(x)
# param_2 = obj.pop()
# param_3 = obj.top()
# param_4 = obj.empty()
