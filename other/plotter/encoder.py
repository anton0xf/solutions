# coding=utf-8
def encode_ascii_image(image):
    # Инициализация начальных значений
    x_pos, y_pos = 0, 0
    commands = []

    for row in image:
        for col, symbol in enumerate(row):
            # Если текущий символ не пробел, то добавляем команды для движения и печати
            if symbol != " ":
                # Добавление команды перемещения пера вправо, если нужно
                move_right = col - x_pos
                if move_right > 0:
                    commands.append("R{}".format(move_right))
                # Добавление команды печати символа
                commands.append("P{}".format(symbol))
                x_pos = col
        # Переход на новую строку, если не последняя строка
        if y_pos < len(image) - 1:
            move_down = 1
            move_left = x_pos
            # Перемещаем перо вниз на одну позицию
            if move_down > 0:
                commands.append("D{}".format(move_down))
            # Перемещение пера в начало следующей строки
            if move_left > 0:
                commands.append("L{}".format(move_left))
            x_pos = 0
            y_pos += 1

    # Вывод расчитанных размеров экрана и команд
    height = len(image)
    width = max(len(row) for row in image)
    print(height)
    print(width)
    print("".join(commands))

# Считывание изображения до ввода пустой строки
image = []
while True:
    line = input()
    if line == "":
        break
    image.append(line)

encode_ascii_image(image)
