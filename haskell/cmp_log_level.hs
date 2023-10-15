{-
https://stepik.org/lesson/4916/step/11?unit=1082

Тип LogLevel описывает различные уровни логирования.

Определите функцию cmp, сравнивающую элементы типа LogLevel так,
чтобы было верно, что Error > Warning > Info.

GHCi> cmp Error Warning
GT
GHCi> cmp Info Warning
LT
GHCi> cmp Warning Warning
EQ
-}

data LogLevel = Error | Warning | Info
  
cmp :: LogLevel -> LogLevel -> Ordering
cmp Error   Error   = EQ
cmp Warning Warning = EQ
cmp Info    Info    = EQ
cmp Error   _       = GT
cmp Warning Info    = GT
cmp _       _       = LT
