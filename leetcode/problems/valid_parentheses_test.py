import problems.valid_parentheses as sol

s = sol.Solution()


def test():
    assert s.isValid("()")
    assert s.isValid("()[]{}")
    assert not s.isValid("(]")
