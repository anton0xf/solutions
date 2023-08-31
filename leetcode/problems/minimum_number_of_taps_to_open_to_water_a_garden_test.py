from problems.minimum_number_of_taps_to_open_to_water_a_garden import Solution


def test():
    s = Solution()
    assert s.minTaps(5, [3, 4, 1, 1, 0, 0]) == 1
    assert s.minTaps(3, [0, 0, 0, 0]) == -1
    assert s.minTaps(19, [4, 1, 5, 0, 5, 3, 3, 3, 0, 0,
                          3, 3, 2, 2, 4, 4, 2, 3, 4, 2]) == 3
