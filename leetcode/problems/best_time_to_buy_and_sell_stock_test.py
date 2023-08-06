import problems.best_time_to_buy_and_sell_stock as sol

s = sol.Solution()


def test():
    assert s.maxProfit([7, 1, 5, 3, 6, 4]) == 5
    assert s.maxProfit([7, 6, 4, 3, 1]) == 0
