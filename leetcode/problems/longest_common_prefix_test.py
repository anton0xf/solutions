from problems.longest_common_prefix import Solution

s = Solution()


def test():
    assert s.longestCommonPrefix(["flower", "flow", "flight"]) == "fl"
    assert s.longestCommonPrefix(["dog", "racecar", "car"]) == ""
    assert s.longestCommonPrefix(["cir", "car"]) == "c"
    assert s.longestCommonPrefix([""]) == ""
