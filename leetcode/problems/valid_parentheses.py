# https://leetcode.com/problems/valid-parentheses/

brackets = {'(': ')', '{': '}', '[': ']'}


class Solution:
    def isValid(self, s: str) -> bool:
        stack = []
        for c in s:
            if c in brackets:
                stack.append(c)
            elif stack:
                head = stack.pop()
                if c != brackets[head]:
                    return False
                # continue
            else:
                return False
        return not stack
