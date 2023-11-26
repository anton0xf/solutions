def distance(str_a, str_b):
    if len(str_a) != len(str_b):
        raise ValueError('String lengths differ')
    return sum(a != b for a, b in zip(str_a, str_b))
