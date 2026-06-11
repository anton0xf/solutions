Require Import Arith Lia.
Import Nat.
From Stdlib Require Import Setoid.
From Stdlib Require Import Morphisms.

Inductive nc :=
| one: nc
| comb: nc -> nc -> nc.

Notation "a ∘ b" := (comb a b) (at level 40, left associativity).

Fixpoint nat2nc (n: nat): nc :=
  match n with
  | 0 => one
  | S n => (nat2nc n) ∘ one
  end.

(* \equiv *)
Reserved Notation "a ≡ b" (at level 70, no associativity).

Inductive nc_eq: nc -> nc -> Prop :=
| nc_eq_refl (a: nc): a ≡ a
| nc_eq_sym (a b: nc): a ≡ b -> b ≡ a
| nc_eq_trans (a b c: nc): a ≡ b -> b ≡ c -> a ≡ c
| nc_eq_comb_l (a b c: nc): a ≡ b -> c ∘ a ≡ c ∘ b
| nc_eq_comb_r (a b c: nc): a ≡ b -> a ∘ c ≡ b ∘ c
| nc_eq_one_comm (a: nc): a ∘ one ≡ one ∘ a
| nc_eq_one_assoc_r (a b: nc): a ∘ (b ∘ one) ≡ (a ∘ b) ∘ one
where "a ≡ b" := (nc_eq a b).

Instance nc_eq_equiv: Equivalence nc_eq.
Proof.
  split.
  - unfold Reflexive. apply nc_eq_refl.
  - unfold Symmetric. apply nc_eq_sym.
  - unfold Transitive. apply nc_eq_trans.
Qed.

Goal (forall n: nc, n ≡ n).
Proof. reflexivity. Qed.

Instance nc_eq_comb_proper: Proper (nc_eq ==> nc_eq ==> nc_eq) comb.
Proof.
  unfold Proper, respectful.
  intros a1 a2 eq_a b1 b2 eq_b.
  apply nc_eq_trans with (a1 ∘ b2).
  - apply nc_eq_comb_l. exact eq_b.
  - apply nc_eq_comb_r. exact eq_a.
Qed.

Theorem sum_correct (m n: nat): nat2nc m ∘ nat2nc n ≡ nat2nc (1 + m + n).
Proof.
  induction n as [|n IH].
  { simpl. rewrite add_0_r. reflexivity. }
  simpl. rewrite add_succ_r.
  replace (S (m + n)) with (1 + m + n) by lia.
  rewrite nc_eq_one_assoc_r. apply nc_eq_comb_r.
  exact IH.
Qed.

Theorem nc_repr (a: nc): exists n: nat, nat2nc n ≡ a.
Proof.
  induction a as [|a1 [n1 IH1] a2 [n2 IH2]].
  { exists 0. simpl. reflexivity. }
  exists (1 + n1 + n2).
  rewrite <- sum_correct.
  rewrite IH1, IH2. reflexivity.
Qed.

Theorem nat2nc_respect : forall m n, m = n -> nat2nc m ≡ nat2nc n.
Proof. intros m n H. subst m. apply nc_eq_refl. Qed.

Theorem nc_eq_comm (a b: nc): a ∘ b ≡ b ∘ a.
Proof.
  destruct (nc_repr a) as [n Ha].
  destruct (nc_repr b) as [m Hb].
  rewrite <- Ha, <- Hb, !sum_correct.
  apply nat2nc_respect. lia.
Qed.

Theorem nc_eq_assoc (a b c: nc): a ∘ (b ∘ c) ≡ (a ∘ b) ∘ c.
Proof.
    destruct (nc_repr a) as [n Ha].
    destruct (nc_repr b) as [m Hb].
    destruct (nc_repr c) as [k Hc].
    rewrite <-Ha, <-Hb, <-Hc, !sum_correct.
    apply nat2nc_respect. lia.
Qed.
  
Theorem nc_eq_one_assoc2 (a b: nc): (a ∘ one) ∘ (b ∘ one) ≡ ((a ∘ b) ∘ one) ∘ one.
Proof.
  rewrite nc_eq_assoc. apply nc_eq_comb_r.
  apply nc_eq_trans with ((one ∘ a) ∘ b).
  { apply nc_eq_comb_r. apply nc_eq_one_comm. }
  apply nc_eq_trans with (one ∘ (a ∘ b)).
  { symmetry. apply nc_eq_assoc. }
  apply nc_eq_sym, nc_eq_one_comm.
Qed.
