import favorite_companies as sol

s = sol.Solution()


def check(expected, favoriteCompanies):
    assert expected == s.peopleIndexes(favoriteCompanies)


def test_ex():
    check([0, 1, 4],
          [["leetcode", "google", "facebook"],
           ["google", "microsoft"],
           ["google", "facebook"],
           ["google"], ["amazon"]])
