From Stdlib Require Import Arith List.
Import Nat Peano.
Import ListNotations.

From Coq Require Import Recdef.
Function digits (n: nat) {wf lt n}: list nat :=
  if n <=? 9 then [n]
  else (n mod 10) :: digits (n / 10).
Proof.
  2: { apply Wf_nat.lt_wf. }
  intros n ngt. apply leb_gt in ngt.
  apply div_lt.
  - apply lt_trans with 9.
    + apply lt_0_succ.
    + exact ngt.
  - rewrite <- succ_lt_mono. apply lt_0_succ.
Qed.

Definition sum (xs: list nat): nat := fold_right add 0 xs.

Theorem sum_cons (x: nat) (xs: list nat): sum (x :: xs) = x + sum xs.
Proof. reflexivity. Qed.

Theorem sum_of_one_digit (n: nat): n <= 9 -> sum (digits n) = n.
Proof.
  functional induction (digits n) as [n _ | n Hgt IH]; intros Hle.
  { unfold sum. simpl. apply add_0_r. }
  apply leb_gt in Hgt. apply lt_nge in Hgt. contradiction.
Qed.

Theorem sum_digit_step (n: nat): 9 < n -> n mod 10 + n / 10 < n.
Proof.
  intro Hlt. rewrite (div_mod_eq n 10) at 3.
  rewrite add_comm. apply add_lt_mono_r_proj_l2r.
  rewrite <- (mul_1_l (n / 10)) at 1.
  apply mul_lt_mono_pos_r.
  - apply div_str_pos_iff. { apply neq_succ_0. }
    apply Hlt.
  - rewrite <- succ_lt_mono. apply lt_0_succ.
Qed.

Theorem sum_digit_dec (n: nat): 9 < n -> sum (digits n) < n.
Proof.
  functional induction (digits n) as [n Hle | n _ IH]; intros H.
  { apply leb_le in Hle. apply le_ngt in Hle. contradiction. }
  rewrite sum_cons. apply le_lt_trans with (n mod 10 + n / 10).
  - apply add_le_mono_l. destruct (le_lt_dec (n / 10) 9) as [H'|H'].
    + rewrite (sum_of_one_digit _ H'). apply le_refl.
    + apply lt_le_incl, IH, H'.
  - apply sum_digit_step. exact H.
Qed.  

Function root (n: nat) {wf lt n}: nat :=
  let s := sum (digits n)
  in if s <=? 9 then s else root s.
Proof.
  2: { apply Wf_nat.lt_wf. }
  intros n Hgt. apply leb_gt in Hgt.
  destruct (le_lt_dec n 9) as [H | H].
  - apply sum_of_one_digit in H as E. rewrite E in Hgt.
    apply le_ngt in H. contradiction.
  - apply sum_digit_dec. exact H.
Qed.

Fixpoint iterate {X: Type} (f: X -> X) (x: X) (n: nat) {struct n}: list X :=
  match n with
  | O => []
  | S n => x :: iterate f (f x) n
  end.

Definition pows2 := iterate (fun x => x * 2) 2 6.

Compute pows2. (* = [2; 4; 8; 16; 32; 64] : list nat *)

Definition roots2 := map root pows2.

Theorem pows_roots_cycle (n: nat): 0 < n -> root (pow n 2) = root (pow (n mod 6) 2).
Proof.
  functional induction (root (n ^ 2)).
  - admit.
  - admit.
Admitted.

Check hd_error (map root pows2).
(* Eval vm_compute in pows2. *)
Eval simpl in (map root pows2).
