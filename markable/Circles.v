Require Import Bool.
Import BoolNotations.

(* https://www.markability.net/ *)
Inductive sign: Set :=
| empty
| cons (x: sign) (y: sign)
| surround (x: sign).

Definition circle: sign := surround empty.
Definition two: sign := surround circle.

(** true means to destroy the tree and false - to spare *)
Definition val := sign -> bool.

Fixpoint repeat (x: sign) (n: nat): sign :=
  match n with
  | O => empty
  | S O => x
  | S n => cons x (repeat x n)
  end.

Definition val_correct (f: val): Prop :=
  f empty = false
  /\ f circle = true
  /\ (forall n: nat, f (repeat circle (S n)) = true)
  /\ f two = false
  /\ f (cons two circle) = true
  /\ f (cons two two) = false
  /\ f (surround (cons circle circle)) = false
  /\ f (surround two) = true.

Fixpoint my_val (x: sign): bool :=
  match x with
  | empty => false
  | cons x y => my_val x || my_val y
  | surround x => negb (my_val x)
  end.

Theorem my_val_correct: val_correct my_val.
Proof.
  unfold val_correct. simpl.
  repeat split; try reflexivity.
  destruct n as [|n]. { reflexivity. }
  simpl. reflexivity.
Qed.

(* https://www.markability.net/reduction.htm *)
Fixpoint son_val (x: sign): bool :=
  match x with
  | empty => false
  | cons x y => if son_val x then true
               else son_val y
  | surround x => negb (son_val x)
  end.

Theorem son_val_eq_my (x: sign): my_val x = son_val x.
Proof. reflexivity. Qed.

Inductive perm: sign -> sign -> Prop :=
| perm_empty: perm empty empty
| perm_surround (x y: sign): perm x y -> perm (surround x) (surround y)
| perm_direct (x1 x2 y1 y2: sign):
  perm x1 y1 -> perm x2 y2 -> perm (cons x1 x2) (cons y1 y2)
| perm_inv (x1 x2 y1 y2: sign):
  perm x1 y1 -> perm x2 y2 -> perm (cons x1 x2) (cons y2 y1).

Theorem perm_preserve_my_val (x y: sign): perm x y -> my_val x = my_val y.
Proof.
  generalize dependent y.
  induction x as [ | x1 IH1 x2 IH2 | x IH]; intros y H.
  - (* x = empty *) inversion H. reflexivity.
  - (* x = cons  *) inversion H; subst x0 x3.
    + (* direct *) simpl. rewrite <- (IH1 y1 H2), <- (IH2 y2 H4). reflexivity.
    + (* inv *) simpl. rewrite <- (IH1 y1 H2), <- (IH2 y2 H4). apply orb_comm.
  - inversion H. subst x0. simpl. rewrite <- (IH y0 H1). reflexivity.
Qed.
