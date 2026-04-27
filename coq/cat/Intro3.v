(* допустим у нас есть какие-то объекты-точки на игровой карте *)
(* для подписей к объектам нам понадобятся строки,
   а для координат возьмём целые числа *)
Require Import String BinInt.
(* мы уже пользовались выше директивой Import,
   которая позволяет не писать имя модуля,
   но модуль обычно ещё нужно подключить,
   для этого есть директива Require, и можно её объединять с Import *)

(* чтобы заработал синтаксис с кавычками, нужно его включить.
   про нотации ещё обязательно поговорим *)
Open Scope string_scope.
Check "test". (* "test" : string *)

(* аналогично, чтобы числа читались как целые, это тоже нужно явно сказать *) 
Open Scope Z_scope.
Check -1. (* -1 : Z *)

(* далее будет два варианта сделать одно и то же.
   так что, чтобы избежать конфилктов имён, объявим вложенные модули *)

Module InductiveObject.

(* теперь можно объявить тип [object] с подписью и двумя координатами *)
Inductive object := mk_object (label: string) (x y: Z): object.
(* я тут явно назвал параметры, но это не обязательно и не особо полезно,
   т.к. никаких геттеров это объявление не создаёт *)
(* поэтому чаще пишут только типы *)
Inductive object' := mk_object': string -> Z -> Z -> object'.
(* эти объявления эквиваленты. сравните *)
Print object.
(* Inductive object : Set :=  mk_object : string -> Z -> Z -> object. *)
Print object'.
(* Inductive object' : Set :=  mk_object' : string -> Z -> Z -> object'. *)

(* раз геттеров нет, надо их написать.
   для этого опять же пригодится паттерн-матчинг *)
Definition obj_label (obj: object): string :=
  match obj with
  | mk_object label _ _ => label
  end.

(* первую разделительную черту можно не писать *)
Definition obj_x (obj: object): Z := match obj with mk_object _ x _ => x end.
(* типы тоже часто выводятся автоматически *)
Definition obj_y obj := match obj with mk_object _ x _ => x end.

(* Ну и конечно конструктор можно использовать
   не только для паттерн-матчинга, но для конструирования.
   использование конструктора выглядит как вызов функции *)
Check mk_object. (* mk_object : string -> Z -> Z -> object *)

Definition zombie := mk_object "Zombie" (-5) 3.
(* унарный минус часто нужно выделять скобками,
   чтобы он не воспринимался как бинарный оператор *)

Check zombie. (* zombie : object *)

(* таким образом можно писать и функции трансформации *)
Definition move (obj: object) (dx dy: Z) :=
  match obj with
  | mk_object label x y => mk_object label (x + dx) (y + dy)
  end.

Compute move zombie 10 0. (* = mk_object "Zombie" 5 3 : object *)

(* вложенные модули надо явно закрывать *)
End InductiveObject.

(* т.к. подобный шаблон встречается давольно часто,
   то для создания записей с именованными полями и готовыми геттерами
   есть отдельная конструкция Record *)
Module RecordObject.

Record object :=
  mk_object {
      obj_label: string;
      obj_x: Z;
      obj_y: Z;
    }.

(* создали такой же тип *)
Check object. (* object : Set *)

(* с таким же конструктором *)
Check mk_object. (* mk_object : string -> Z -> Z -> object *)

(* но сразу с геттерами *)
Check obj_label. (* obj_label : object -> string *)

(* и альтернативным синтаксисом конструирования *)
Definition zombie :=
  {| (* имена полей задаются явно, так что их можно указывать в любом порядке *) 
    obj_x := (-5);
    obj_y := 3;
    obj_label := "Zombie"
  |}.

(* а также альтернативным синтаксисом для доступа к полям *)
Compute zombie.(obj_label). (* = "Zombie" : string *)

(* синтаксис с такими скобками можно использовать и при паттерн-матчинге *)
Check match zombie with
      | {| obj_x := x; obj_y := y |} => (x, y)
      end.
(* где [(x, y)] - это такой встроенный синтаксис для пар,
   разворачивающийся в [pair x y] *)
Print pair.
(* Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B. *)

(* Т.е. prod - это ещё один пример индуктивного типа с одним конструктором (pair),
   но дополнительно параметризованного ещё и типами своих элементов *)

End RecordObject.
