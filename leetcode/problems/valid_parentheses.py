# https://leetcode.com/problems/valid-parentheses/

brackets = {'(': ')', '{': '}', '[': ']'}

open_brakets = set(brackets.keys())

close_brackets = {v: k for (k, v) in brackets.items()}


class Solution:
    def isValid(self, s: str) -> bool:
        stack = []
        for c in s:
            if c in open_brakets:
                stack.append(c)
            elif stack:
                head = stack.pop()
                if close_brackets[c] != head:
                    return False
                # continue
            else:
                return False
        return not stack
