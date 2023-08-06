# https://leetcode.com/problems/best-time-to-buy-and-sell-stock/
from typing import List


class Solution:
    def maxProfit(self, prices: List[int]) -> int:
        min_price = prices[0]
        profit = 0
        for price in prices:
            if price < min_price:
                min_price = price
            else:
                diff = price - min_price
                if diff > profit:
                    profit = diff
        return profit
