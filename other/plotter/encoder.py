# coding=utf-8
def encode_ascii_image(image):
    # Определение размеров экрана
    height = len(image)
    width = max(len(row) for row in image)

    # Инициализация начальных значений
    x_pos, y_pos = 0, 0
    commands = []

    for row in image:
        for col, symbol in enumerate(row):
            # Если текущий символ не пробел, переместимся к нему и напечатаем
            if symbol != " ":
                move_right = col - x_pos
                if move_right > 0:
                    # Добавление команды перемещения вправо
                    commands.append(f"R{move_right}")
                # Добавление команды печати
                commands.append(f"P{symbol}")
                x_pos = col
        # Переход к новой строке, если это не последняя строка
        if y_pos < height - 1:
            move_down = 1
            move_left = x_pos
            if move_down > 0:
                commands.append(f"D{move_down}")
            if move_left > 0:
                commands.append(f"L{move_left}")
            x_pos = 0
            y_pos += 1

    # Вывод размеров экрана
    print(height)
    print(width)
    # Вывод списка команд в одну строку
    print("".join(commands))


# Пример ввода
ascii_image_example = [
    "   ***",
    "   * *",
    "   ***"
]

encode_ascii_image(ascii_image_example)
