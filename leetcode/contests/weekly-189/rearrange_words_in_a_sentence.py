class Solution:
    def arrangeWords(self, text: str) -> str:
        words = sorted(text.lower().split(), key=len)
        if words:
            words[0] = words[0].capitalize()
        return ' '.join(words)
