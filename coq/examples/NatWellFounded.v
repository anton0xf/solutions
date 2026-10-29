Require Import Arith.

Definition minp (P: nat -> Prop) (k: nat) := P k /\ forall m, m < k -> ~ P m.

Theorem nat_well_founded (P: nat -> Prop) (HP: forall x, P x \/ ~ P x):
  (exists n, P n) -> exists k, minp P k.
Proof.
  intros [n HPn]. 
  assert (forall x, (forall m, m <= x -> ~ P m) \/ (exists k, k <= x /\ minp P k)) as H.
  { induction x as [| x IH].
    - destruct (HP 0) as [H | H].
      + right. exists 0. split. { apply le_n. }
        split. { exact H. }
        intros m Hm. inversion Hm.
      + left. intros m Hm. inversion Hm. exact H.
    - destruct IH as [IH | IH].
      + destruct (HP (S x)) as [H | H].
        * right. exists (S x). split. { apply le_n. }
          split. { exact H. }
          intros m Hm. apply PeanoNat.lt_n_Sm_le in Hm.
          apply IH, Hm.
        * left. intros m Hm. inversion Hm. { exact H. }
          subst m0. apply IH. assumption.
      + right. destruct IH as [k [Hk H]].
        exists k. split; [| exact H]. apply le_S, Hk. }
  destruct (H n) as [Hc | [k [Hk HPk]]].
  { contradict HPn. apply Hc. apply le_n. }
  exists k. exact HPk.
Qed.

Theorem nat_well_founded_implies_LEM:
  (forall P: nat -> Prop, (exists n, P n) -> exists k, minp P k) ->
  forall A: Prop, A \/ ~ A.
Proof.
  intros H A.
  pose (P := fun n: nat => (n = 0 /\ A) \/ n = 1).
  assert (Hex : exists n, P n).
  { exists 1. right. reflexivity. }
  destruct (H P Hex) as [k [Hk Hmin]].
  unfold P in Hk. destruct Hk as [[_ HA] | Hk].
  - left. exact HA.
  - right. intro HA. subst k. apply (Hmin 0). { apply Nat.lt_0_1. }
    left. split; [reflexivity | exact HA].
Qed.
