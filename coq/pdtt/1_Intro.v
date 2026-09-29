Require Import Arith.

Inductive Vec (A: Set): nat -> Set :=
| vnil: Vec A 0
| vcons (n: nat): A -> Vec A n -> Vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} {n}.

Notation "[ ]" := vnil.
Infix "::" := vcons (at level 60, right associativity).

Definition head {A: Set} {n: nat} (xs: Vec A (S n)): A :=
  match xs with
  | x :: _ => x
  end.
  
Definition tail {A: Set} {n: nat} (xs: Vec A (S n)): Vec A n :=
  match xs with
  | _ :: xs => xs
  end.

Fixpoint append {A: Set} {n m: nat} (xs: Vec A n) (ys: Vec A m): Vec A (n + m) :=
  match xs with
  | [] => ys
  | x :: xs => x :: append xs ys
  end.
