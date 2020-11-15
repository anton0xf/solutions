class Solution:
    def busyStudent(self, startTime, endTime, queryTime):
        return sum(s <= queryTime <= e for s, e in zip(startTime, endTime))
