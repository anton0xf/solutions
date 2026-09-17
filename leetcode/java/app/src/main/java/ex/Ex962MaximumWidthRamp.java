package ex;

import java.util.ArrayDeque;
import java.util.Deque;

/* https://leetcode.com/problems/maximum-width-ramp */
public class Ex962MaximumWidthRamp {
    public int maxWidthRamp(int[] nums) {
        Deque<Integer> mins = new ArrayDeque<>();
        mins.push(0);
        int maxWidth = 0;
        for (int i = 1; i < nums.length; i++) {
            //noinspection DataFlowIssue
            if(nums[i] < nums[mins.peek()]) {
                mins.push(i);
            }
        }
        for (int i = nums.length - 1; i >= 0; i--) {
            while(!mins.isEmpty() && nums[mins.peek()] <= nums[i]) {
                int j = mins.pop();
                maxWidth = Math.max(maxWidth, i - j);
            }
        }
        return maxWidth;
    }
}
