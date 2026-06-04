Require Import String BinInt.
Open Scope string_scope.

Record dep_object :=
  mk_dep_object {
      T: Type;
      value: T;
      x: Z; y: Z;
    }.

Definition zombie_obj :=
  {|
    T := string;
    value := "Zombie";
    x := 5; y := 3;
  |}.

Definition first_obj :=
  {|
    T := nat;
    (* первое натуральное число - это, конечно, 0 *)
    value := 0;
    x := 0; y := 0;
  |}.

Record cat :=
  mk_cat {
      ob: Type;
      hom: ob -> ob -> Type;
    }.

    

