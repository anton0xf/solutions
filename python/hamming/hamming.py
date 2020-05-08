def distance(str_a, str_b):
    if len(str_a) != len(str_b):
        raise ValueError('String lengths differ')
    return sum(1 for a, b in zip(str_a, str_b) if a != b)
