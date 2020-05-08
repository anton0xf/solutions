import problems.longest_substring_without_repeating_characters as sol

s = sol.Solution()


def test_example1():
    assert 3 == s.lengthOfLongestSubstring('abcabcbb')


def test_example2():
    assert 1 == s.lengthOfLongestSubstring('bbbbb')


def test_example3():
    assert 3 == s.lengthOfLongestSubstring('pwwkew')
