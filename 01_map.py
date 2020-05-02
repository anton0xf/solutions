#!/usr/bin/env python3
s = '''g fmnc wms bgblr rpylqjyrc gr zw fylb.
rfyrq ufyr amknsrcpq ypc dmp.
bmgle gr gl zw fylb gq glcddgagclr ylb rfyr'q ufw rfgq rcvr gq qm jmle.
sqgle qrpgle.kyicrpylq() gq pcamkkclbcb. lmu ynnjw ml rfc spj.'''

# rules = {'k': 'm', 'o': 'q', 'e': 'g'}
# [ord(rules[c]) - ord(c) for c in rules] == [2, 2, 2]


def map_char(c):
    if not (ord('a') <= ord(c) <= ord('z')):
        return c
    n = ord(c) + 2
    if n > ord('z'):
        n = n - ord('z') + ord('a') - 1
    return chr(n)


def map_str(s):
    return ''.join(map_char(c) for c in s)


if __name__ == '__main__':
    print(map_str(s))
