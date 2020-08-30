def get(a1, n):
    a = a1
    nums = {}
    for i in range(n):
        b = i - nums[a] if a in nums else 0
        nums[a] = i
        a = b
    return a


if __name__ == '__main__':
    a1 = int(input())
    n = int(input())
    print(get(a1, n - 1))
