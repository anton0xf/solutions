# coding=utf-8
import sys


def encode_ascii_image(image):
    # Инициализация начальных значений
    x_pos, y_pos = 0, 0
    commands = []
    height = len(image)
    width = max(len(row) for row in image)

    for row in image:
        for col, symbol in enumerate(row.ljust(width)):
            # Если символ не пробел, создаем команду для перемещения и печати
            if symbol != ' ':
                move_right = col - x_pos
                if move_right > 0:
                    commands.append('R{}'.format(move_right))
                commands.append('P{}'.format(symbol))
                x_pos = col

        # Если это не последняя строка, переходим на новую строку
        if y_pos < height - 1:
            commands.append('D1')
            if x_pos > 0:
                commands.append('L{}'.format(x_pos))
            x_pos = 0
            y_pos += 1

    # Возвращаем результат: размеры и команды
    return height, width, ''.join(commands)


# Чтение изображения из стандартного входа до EOF
image_input = sys.stdin.readlines()
image = [line.rstrip('\n') for line in image_input]

height, width, command_string = encode_ascii_image(image)
print(height)
print(width)
print(command_string)
