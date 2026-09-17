package ex;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Ex121BestTimeToBuyTest {
    private Ex121BestTimeToBuy solution = new Ex121BestTimeToBuy();

    @Test
    @DisplayName("Buy on day 2 (price = 1) and sell on day 5 (price = 6), profit = 6-1 = 5.")
    void example1() {
        assertEquals(5, solution.maxProfit(new int[]{7, 1, 5, 3, 6, 4}));
    }

    @Test
    @DisplayName("no transactions are done and the max profit = 0")
    void example2() {
        assertEquals(0, solution.maxProfit(new int[]{7, 6, 4, 3, 1}));
    }
}