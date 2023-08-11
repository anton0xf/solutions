import problems.palindrome_number as sol

s = sol.Solution()


def test():
    assert s.isPalindrome(121)
    assert not s.isPalindrome(-121)
    assert not s.isPalindrome(10)
