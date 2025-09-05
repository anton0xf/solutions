Require Import Setoid.
From Stdlib Require Import Classical.

Parameter NSet : Type.
Parameter NIn : NSet -> NSet -> Prop.
Notation "a ∈ b" := (NIn a b) (at level 70, no associativity).

Check (forall a b: NSet, NIn a b).

(** Definition 1.1.1. *)
Axiom Aeq: forall a b: NSet, a = b <-> forall x, x ∈ a <-> x ∈ b.

Parameter Subset : NSet -> NSet -> Prop.
Notation "a ⊆ b" := (Subset a b) (at level 70, no associativity).
Axiom Asub: forall a b: NSet, a ⊆ b <-> forall x, x ∈ a -> x ∈ b.

Parameter ProperSubset : NSet -> NSet -> Prop.
Notation "a ⊂ b" := (ProperSubset a b) (at level 70, no associativity).
Axiom Apsub: forall a b: NSet, a ⊂ b <-> (a ⊆ b /\ ~ a = b).

Parameter EmptySet : NSet.
Notation "∅" := (EmptySet) (at level 0, no associativity).
Check EmptySet.
Axiom Aempty : forall x, ~ x ∈ ∅.

(* disjoint *)
Definition Disj (a b: NSet) := forall x, (x ∈ a -> ~ x ∈ b) /\ (x ∈ b -> ~ x ∈ a).
(** End Definition 1.1.1. *)

Theorem Subset_refl (a: NSet): a ⊆ a.
Proof. rewrite Asub. intros x H. exact H. Qed.

Theorem Empty_Subset (a: NSet): ∅ ⊆ a.
Proof. rewrite Asub. intros x H. contradict H. apply Aempty. Qed.

Theorem Subset_antisym (a b: NSet): a ⊆ b -> b ⊆ a -> a = b.
Proof.
  rewrite !Asub. intros H1 H2. rewrite Aeq.
  intro x. split; intro H; auto.
Qed.

Theorem Empty_uniq (a: NSet): a = ∅ <-> forall x, ~ x ∈ a.
Proof.
  split; intro H.
  - rewrite H. apply Aempty.
  - apply Aeq. intro x. split; intro H1.
    + contradict H1. apply H.
    + contradict H1. apply Aempty.
Qed.

Lemma Disj_sym_aux (a b: NSet): Disj a b -> Disj b a.
Proof. unfold Disj. intros H x. rewrite and_comm. apply H. Qed.

Theorem Disj_sym (a b: NSet): Disj a b <-> Disj b a.
Proof. split; apply Disj_sym_aux. Qed.

Theorem Disj_prop (a b: NSet): Disj a b <-> forall x, x ∈ a -> ~ x ∈ b.
Proof.
  unfold Disj. split; intro H.
  - intros x Ha. apply H. exact Ha.
  - intro x. split.
    + intro Ha. auto.
    + intros Hb Ha. exact (H x Ha Hb).
Qed.

Parameter Separate: (NSet -> Prop) -> NSet.
Notation "{ x | P }" := (Separate (fun x => P)).
Axiom Asep: forall y P, y ∈ { x | P x } <-> P y.

Theorem eq_Separate (a: NSet): a = { x | x ∈ a }.
Proof. rewrite Aeq. intro x. rewrite Asep. reflexivity. Qed.

(** Definition 1.1.2. Power Set *)
Definition Pow (a: NSet): NSet := { x | x ⊆ a }.

(** Definition 1.1.3. *)
Definition Union (a b: NSet) := { x | x ∈ a \/ x ∈ b }.
Notation "x ∪ y" := (Union x y) (at level 50, left associativity).

(* intresection *)
Definition Intr (a b: NSet) := { x | x ∈ a /\ x ∈ b }.
Notation "x ∩ y" := (Intr x y) (at level 45, left associativity).

(* difference *)
Definition Diff (a b: NSet) := { x | x ∈ a /\ ~ x ∈ b }.
Notation "x \ y" := (Diff x y) (at level 40, left associativity).
(** End Definition 1.1.3. *)

Theorem Disj_by_Intr (a b: NSet): Disj a b <-> a ∩ b = ∅.
Proof.
  unfold Disj. rewrite Empty_uniq. split; intro H.
  - intros x. unfold Intr. rewrite Asep.
    intros [Ha Hb]. apply (proj1 (H x)); assumption.
  - intro x. pose (H x) as Hx. unfold Intr in Hx. rewrite Asep in Hx.
    split; auto.
Qed.

Theorem Diff_nothing (A B: NSet): A ∩ B = ∅ -> A \ B = A.
Proof.
  rewrite <- Disj_by_Intr. rewrite Disj_prop. intro H.
  unfold Diff. rewrite Aeq. intro x. rewrite Asep. split.
  - intros [HA _]. exact HA.
  - intro HA. split; auto.
Qed.

(** Exercises 1.1 *)
Theorem Ex1_1_1 (A B: NSet): forall a, ~ a ∈ A \ B -> a ∈ A -> a ∈ B.
Proof.
  intros a Hnd Ha. unfold Diff in Hnd. rewrite Asep in Hnd.
  apply not_and_or in Hnd as [H | H].
  - contradiction.
  - apply NNPP, H.
Qed.

Theorem Ex1_1_2 (A B C: NSet): A ⊆ B -> C \ B ⊆ C \ A.
Proof.
  rewrite !Asub. intros H x. unfold Diff. rewrite !Asep.
  intros [HC HnB]. split. { exact HC. } (* apply contraposition to H *)
  intro HA. apply HnB. apply H, HA.
Qed.

Theorem Ex1_1_3 (A B C: NSet): A \ B ⊆ C -> A \ C ⊆ B.
Proof.
  rewrite !Asub. intros H x HAnC.
  unfold Diff in HAnC. rewrite Asep in HAnC. destruct HAnC as [HA HnC].
  destruct (classic (x ∈ B)) as [HB | HnB]. { exact HB. }
  exfalso. apply HnC. apply H.
  unfold Diff. rewrite Asep. split; assumption.
Qed.

Theorem Ex1_1_4 (A B C: NSet): A ⊆ B -> A ⊆ C -> A ⊆ B ∩ C.
Proof.
  rewrite !Asub. intros HAB HAC x HA. unfold Intr. rewrite Asep.
  split; auto.
Qed.

Theorem Ex1_1_5 (A B C: NSet): A ⊆ B -> B ∩ C = ∅ -> A ⊆ B \ C.
Proof.
  intros HAB HdBC. rewrite (Diff_nothing B C HdBC). exact HAB.
Qed.

Theorem Ex1_1_6 (A B C: NSet): A \ (B \ C) ⊆ (A \ B) ∪ C.
Proof.
  apply Asub. unfold Diff.
  intros x. unfold Union. rewrite !Asep. intros [HA H].
  destruct (classic (x ∈ C)) as [HC | HnC]. { right. exact HC. }
  left. split. { exact HA. }
  intro HB. apply H. auto.
Qed.
  
