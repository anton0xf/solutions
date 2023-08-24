from problems.valid_palindrome import Solution

s = Solution()


def test():
    assert s.isPalindrome("A man, a plan, a canal: Panama")
    assert not s.isPalindrome("race a car")
    assert s.isPalindrome(" ")
