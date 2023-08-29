from problems.minimum_penalty_for_a_shop import Solution


def test():
    s = Solution()
    assert s.bestClosingTime("YYNY") == 2
    assert s.bestClosingTime("NNNNN") == 0
    assert s.bestClosingTime("YYYY") == 4
