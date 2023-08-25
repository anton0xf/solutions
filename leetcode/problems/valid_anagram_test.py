from problems.valid_anagram import Solution

s = Solution()


def test():
    assert s.isAnagram("anagram", "nagaram")
    assert not s.isAnagram("rat", "car")
