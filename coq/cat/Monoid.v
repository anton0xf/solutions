Require Import Cat.

Record monoid :=
  mk_monoid {
      mval: Type;
      mcomp: mval -> mval -> mval where "f * g" := (mcomp f g);
      mid: mval;
      mid_left (x: mval): mid * x = x;
      mid_right (x: mval): x * mid = x;
      massoc (x y z: mval): x * (y * z) = (x * y) * z;
    }.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with monoid.
Bind Scope monoid_scope with monoid.

Arguments mval {_}.
Arguments mcomp {_}.
Arguments mid {_}.
Arguments mid_left {_}.
Arguments mid_right {_}.
Notation "f * g" := (mcomp g f): monoid_scope.

Local Open Scope monoid_scope.
Check (fun (M: monoid) (f g: M.(mval)) => f * g).

Definition monoid_as_cat (M: monoid): cat.
Proof.
  refine {|
      ob := unit;
      hom _ _ := M.(mval);
      comp _ _ _ x y := x * y;
      id _ := mid;
      id_left _ _ x := mid_left x;
      id_right _ _ x := mid_right x;
    |}.
  intros. apply massoc.
Defined.

Definition singleton: cat.
Proof.
  apply monoid_as_cat.
  refine {|
      mval := unit;
      mcomp _ _ := tt;
      mid := tt;
    |}; intro x; destruct x; reflexivity.
Defined.
