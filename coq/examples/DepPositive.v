Require Import Arith.
Import Nat.

Inductive pos := from_pos (n: nat) (p: n > 0).

Definition pval (x: pos): nat :=
  match x with
  | from_pos n p => n
  end.

Theorem pos_div_mul (a: nat) (b: pos): a * pval b / pval b = a.
Proof.
  destruct b as [x p]. simpl.
  apply div_mul. apply neq_0_lt_0. apply p.
Qed.
