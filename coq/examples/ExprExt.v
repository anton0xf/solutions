Require Import Arith List.
Import ListNotations.

Inductive expr := e_num (n: nat) | e_add (e1 e2: expr).

Fixpoint eval (e: expr): nat :=
  match e with
  | e_num n => n
  | e_add e1 e2 => eval e1 + eval e2
  end.

Coercion e_num : nat >-> expr.
Declare Custom Entry expr_entry.
Declare Scope expr_scope.
Notation "<{ e }>" := e (e custom expr_entry) : expr_scope.
Notation "x" := x (in custom expr_entry at level 0,
                      x constr at level 0).
Notation "f x .. y" :=
  (.. (f x) .. y)
    (in custom expr_entry at level 0, only parsing,
        f constr at level 0, x constr at level 1,
        y constr at level 1).
Notation "x + y" := (e_add x y) (in custom expr_entry at level 50,
                          left associativity).
Open Scope expr_scope.

Check <{ 1 + 2 }>.
Check <{ S 1 + 2 }>.

Example eval_ex1: eval <{ 1 + 2 }> = 3.
Proof. reflexivity. Qed.
