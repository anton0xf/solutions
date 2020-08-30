#!/usr/bin/python3
# http://www.pythonchallenge.com/pc/def/ocr.html
import urllib.request
from html.parser import HTMLParser
from collections import Counter

url = 'http://www.pythonchallenge.com/pc/def/ocr.html'


def get_page(url):
    with urllib.request.urlopen(url) as resp:
        return resp.read().decode("utf8")


class CommentsHTMLParser(HTMLParser):

    lim = 20
    comments = []

    def handle_comment(self, comment):
        self.comments.append(comment)

    def get_comments(self):
        return self.comments


def parse_page(page):
    parser = CommentsHTMLParser()
    parser.feed(page)
    return parser.get_comments()


if __name__ == '__main__':
    page = get_page(url)
    comments = parse_page(page)
    comment = comments[1]
    chars = list(comment)
    cnt = Counter(chars)
    rare = set(k for k, v in cnt.items() if v == 1)
    print(''.join(c for c in comment if c in rare))
