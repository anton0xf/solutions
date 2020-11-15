from typing import List


class Solution:
    def peopleIndexes(self, favoriteCompanies: List[List[str]]) -> List[int]:
        index = [set(v) for v in favoriteCompanies]
        return [i for i, v in enumerate(index)
                if not any(v.issubset(s)
                           for j, s in enumerate(index)
                           if j != i)]
