package ex;

/* https://leetcode.com/problems/best-time-to-buy-and-sell-stock/ */
public class Ex121BestTimeToBuy {
    public int maxProfit(int[] prices) {
        int maxProfit = 0;
        int min = prices[0];
        for (int j = 1; j < prices.length; j++) {
            min = Math.min(min, prices[j]);
            maxProfit = Math.max(maxProfit, prices[j] - min);
        }
        return maxProfit;
    }
}
