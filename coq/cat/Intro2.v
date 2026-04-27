(* можно объявлять пользовательские типы-перечисления *)
Inductive color := red | green | blue.

(* и делать по ним pattern-matching *)
Definition red_or_blue (c: color): bool :=
  match c with
  | red => true
  | green => false
  | blue => true
  end.

Compute red_or_blue red. (* = true : bool *)

(* В паттерн-матчинге могут быть разные шаблоны,
   включающие в т.ч. плейсхолдер [_],
   что часто позволяет сократить описание *)
Definition red_or_blue' (c: color): bool :=
  match c with
  | green => false
  | _ => true
  end.
(* да, в именах можно использовать апостроф, и этим активно пользуются *)

(* можно включать в паттерн-матчинг несколько значений сразу *)
Definition eqb_color (c1 c2: color): bool :=
  match c1, c2 with
  | red, red => true
  | green, green => true
  | blue, blue => true
  | _, _ => false
  end.

(* Print работает и для библиотечных определений *)
Print bool. (* Inductive bool : Set :=  true : bool | false : bool. *)
(* Здесь Set - это не то же самое, что множество в классической математике,
   это такой наименьший тип типов, т.е. тип индуктивных типов и функций над ними *)
Check bool. (* bool : Set *)
Check color. (* color : Set *)
Check eqb_color. (* eqb_color : color -> color -> bool *)
Check color -> color -> bool. (* color -> color -> bool : Set *)

(* сам он имеет тип Type *)
Check Set. (* Set : Type *)
(* там немного сложнее внутри это устроено, чтобы избежать парадоксов,
   но это пока не особо важно *)
