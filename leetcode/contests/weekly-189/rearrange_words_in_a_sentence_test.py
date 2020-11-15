import rearrange_words_in_a_sentence as sol

s = sol.Solution()


def check(expected, text):
    assert expected == s.arrangeWords(text)


def test_ex():
    check("Is cool leetcode", "Leetcode is cool")
    check("On and keep calm code", "Keep calm and code on")
    check("To be or to be not", "To be or not to be")
