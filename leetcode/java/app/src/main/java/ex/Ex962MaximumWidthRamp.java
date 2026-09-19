package ex;

import java.util.ArrayDeque;
import java.util.Deque;

/* https://leetcode.com/problems/maximum-width-ramp */
public class Ex962MaximumWidthRamp {
    public int maxWidthRamp(int[] nums) {
        Deque<Integer> minIds = new ArrayDeque<>();
        minIds.push(0);
        for (int i = 1; i < nums.length; i++) {
            //noinspection DataFlowIssue
            if(nums[i] < nums[minIds.peek()]) {
                minIds.push(i);
            }
        }

        int maxWidth = 0;
        for (int j = nums.length - 1; j > 0; j--) {
            while(!minIds.isEmpty() && nums[minIds.peek()] <= nums[j]) {
                int i = minIds.pop(); // i <= j
                maxWidth = Math.max(maxWidth, j - i);
            }
        }
        return maxWidth;
    }
}
