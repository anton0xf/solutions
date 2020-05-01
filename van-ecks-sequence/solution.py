import itertools as it


def gen(a1):
    a = a1
    nums = {}
    for i in it.count():
        yield a
        b = i - nums[a] if a in nums else 0
        nums[a] = i
        a = b


if __name__ == '__main__':
    a1 = int(input())
    n = int(input())
    print(next(it.islice(gen(a1), n-1, n)))
