Tasks: https://t.me/progmsk/163625

# Задача №1. Кодирование
Реализовать кодировщик ASCII-изображений. 
Для кодирования используем вымышленный автомат, состоящий из экрана и пера,
которое умеет выполнять команды.
Команда перемещения пера состоит из буквы U, R, D или L, сразу за которой может следовать одна
или больше цифр, например, U, R5, D12, L203 — команды перемещения.
Команда U означает перемещение пера на одну клетку вверх, R — вправо, D — вниз и L — влево.
Число показывает, сколько раз надо повторить команду, R5 означает перемещение пера
на пять клеток вправо.
Команда печати состоит из буквы P, сразу за которой следует ровно один печатный ASCII-символ.
Например, P1, P*, P@ — команды печати.
Экран — это прямоугольная область, состоящая из клеток, в каждой из которых может быть
напечатан ASCII-символ. В начале работы программы все клетки экрана пустые (содержат пробел),
а перо находится в левом верхнем углу. Программа должна по готовому изображению построить
набор команд для автомата.
Программа получает на вход ASCII-изображение, содержащие печатные ASCII-символы.
Каждая строка изображения соответствует одной входной строке. Правый край не обязательно
будет ровным, то есть ширина строк может различаться. Некоторые строки могут быть пустыми.

Пример входа программы:
```

   ***
   * *
   ***
```

В примере на экране нарисован квадрат размером 3*3.

Программа должна определить размеры экрана (в данном случае высота и ширина равны 4✕6),
и закодировать изображение с помощью команд. Программа-кодировщик печатает в отдельных
строках высоту и ширину экрана, и затем — в третьей строке — код. Код состоит из команд,
которые записаны друг за другом без разделителей. Пример.
```
4
6
DR4P*RP*RP*DP*DP*LP*LP*UP*
```

# Задача №2. Декодирование
Реализовать декодировщик ASCII-изображений.
Для декодирования используем вымышленный автомат, состоящий из экрана и пера,
которое умеет выполнять команды.
Команда перемещения пера состоит из буквы U, R, D или L, сразу за которой может следовать
одна или больше цифр, например, U, R5, D12, L203 — команды перемещения.
Команда U означает перемещение пера на одну клетку вверх, R — вправо, D — вниз и L — влево.
Число показывает, сколько раз надо повторить команду, R5 означает перемещение
пера на пять клеток вправо.
Команда печати состоит из буквы P, сразу за которой следует ровно один печатный ASCII-символ.
Например, P1, P*, P@ — команды печати.
Экран — это прямоугольная область, состоящая из клеток, в каждой из которых может быть
напечатан ASCII-символ. В начале работы программы все клетки экрана пустые (содержат пробел),
а перо находится в левом верхнем углу. Программа должна по набору команд построить изображение.
Программа получает на вход три строки. В первой строке находится высота экрана, во второй ширина,
а в третьей — код. Код состоит из команд, которые записаны друг за другом без разделителей.

Пример входа программы:
```
4
6
DR4P*RP*RP*DP*DP*LP*LP*UP*
```
Программа должна нарисовать изображение и напечатать его. В данном случае должно получиться
4 строки. Пробелы справа в правой части строки можно обрезать.

Пример вывода программы:
```

   ***
   * *
   ***
```

Да, вот текстовые примеры для тестирования:

```
      -''--.
       _`>   `\.-'<
    _.'     _     '._
  .'   _.='   '=._   '.
  >_   / /_\ /_\ \   _<
    / (  \o/\\o/  ) \
    >._\ .-,_)-. /_.<
jgs     /__/ \__\ 
          '---'     E=mc^2
```

```
9
26
R6P-RP'RP'RP-RP-RP.L11DR7P_RP`RP>R4P`RP\RP.RP-RP'RP<L18DR4P_RP.RP'R6P_R6P'RP.RP_L20DR2P.RP'R4P_RP.RP=RP'R4P'RP=RP.RP_R4P'RP.L22DR2P>RP_R4P/R2P/RP_RP\R2P/RP_RP\R2P\R4P_RP<L22DR4P/R2P(R3P\RPoRP/RP\RP\RPoRP/R3P)R2P\L20DR4P>RP.RP_RP\R2P.RP-RP,RP_RP)RP-RP.R2P/RP_RP.RP<L20DR0PjRPgRPsR6P/RP_RP_RP/R2P\RP_RP_RP\L17DR10P'RP-RP-RP-RP'R6PERP=RPmRPcRP^RP2
```

После декодирования должен получиться Эйнштейн. Ваш код не обязательно должен быть точно
таким же, главное, чтобы давал правильный результат.

# Examples
```console
$ ./encoder.bb <test-field1.txt
4
6
DR3P*RP*RP*DL2P*R2P*DL2P*RP*RP*

$ <test-field1.txt ./encoder.bb | ./decoder.bb
      
   ***
   * *
   ***
```

## Python version from AI
```console
$ <test-field1.txt python3 encoder.py | python3 decoder.py

   ***
   * *
   ***
```
