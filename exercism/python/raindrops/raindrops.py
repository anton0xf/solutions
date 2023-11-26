# list of tuples: (factor, sound)
RULES = [(3, 'Pling'), (5, 'Plang'), (7, 'Plong')]


def convert(n):
    sounds = [sound
              for (factor, sound) in RULES
              if n % factor == 0]
    return ''.join(sounds) if sounds else str(n)
