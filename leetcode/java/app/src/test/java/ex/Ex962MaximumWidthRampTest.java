package ex;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class Ex962MaximumWidthRampTest {
    private Ex962MaximumWidthRamp solution = new Ex962MaximumWidthRamp();

    @Test
    @DisplayName("simplest")
    void example0() {
        assertEquals(2, solution.maxWidthRamp(new int[]{0, 2, 1}));
    }

    @Test
    @DisplayName("The maximum width ramp is achieved at (i, j) = (1, 5): nums[1] = 0 and nums[5] = 5")
    void example1() {
        assertEquals(4, solution.maxWidthRamp(new int[]{6, 0, 8, 2, 1, 5}));
    }

    @Test
    @DisplayName("The maximum width ramp is achieved at (i, j) = (2, 9): nums[2] = 1 and nums[9] = 1")
    void example2() {
        assertEquals(7, solution.maxWidthRamp(new int[]{9, 8, 1, 0, 1, 9, 4, 0, 4, 1}));
    }
}