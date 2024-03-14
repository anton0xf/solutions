# coding=utf-8
def draw_image(height, width, commands):
    # Создаем экран из пробелов
    screen = [[' ' for _ in range(width)] for _ in range(height)]
    x, y = 0, 0  # Начальные координаты пера

    i = 0
    while i < len(commands):
        command = commands[i]
        i += 1
        if command in 'UDLR':  # Если команда перемещения
            # Если за ней стоит число
            if i < len(commands) and commands[i].isdigit():
                # Считываем всё число
                num = ''
                while i < len(commands) and commands[i].isdigit():
                    num += commands[i]
                    i += 1
                distance = int(num)
            else:  # Если за командой не стоит число, значит перемещение на 1
                distance = 1

            # Перемещаем перо в зависимости от команды
            if command == 'U':
                y = max(0, y - distance)
            elif command == 'D':
                y = min(height - 1, y + distance)
            elif command == 'L':
                x = max(0, x - distance)
            elif command == 'R':
                x = min(width - 1, x + distance)

        elif command == 'P':  # Если команда печати
            if i < len(commands):
                screen[y][x] = commands[i]
                i += 1

    # Печатаем получившееся изображение
    for row in screen:
        print("".join(row).rstrip())


# Входные данные
height = int(input())
width = int(input())
commands = input()

draw_image(height, width, commands)
