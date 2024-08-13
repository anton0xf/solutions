Require Import Arith.
Import Nat.

(* 2.4.2 Principle of complete induction on natural numbers *)
Lemma complete_induction' (P: nat -> Prop):
  (forall n: nat, (forall i: nat, i < n -> P i) -> P n) -> forall n i: nat, i <= n -> P i.
Proof.
  intros H n.
  induction n as [| n IH].
  - intros i Hle. apply H. intros j Hlt.
    apply (lt_le_trans j i 0 Hlt) in Hle as Hlt0.
    contradict Hlt0. apply nlt_0_r.
  - intros i Hle.
    apply lt_eq_cases in Hle as [Hle|Heq].
    + apply IH. apply lt_succ_r, Hle.
    + subst i. apply H. intros i.
      rewrite lt_succ_r. apply IH.
Qed.

Theorem complete_induction (P: nat -> Prop):
  (forall n: nat, (forall i: nat, i < n -> P i) -> P n) -> forall n: nat, P n.
Proof.
  intros H n. apply (complete_induction' P H n n). apply le_n.
Qed.

(* 2.4.4 Principle of lexicographic induction *)
Definition le_pair (p q: nat * nat): Prop := fst p < fst q \/ (fst p = fst q /\ snd p <= snd q).
Definition lt_pair (p q: nat * nat): Prop := le_pair p q /\ p <> q.

Theorem pair_neq (p q: nat * nat): p <> q <-> fst p <> fst q \/ snd p <> snd q.
Proof.
  unfold not at 1.
  rewrite surjective_pairing at 1. rewrite (surjective_pairing q) at 1.
  rewrite pair_equal_spec. split; intros H.
  - destruct (eq_dec (fst p) (fst q)) as [eq1|neq1];
    destruct (eq_dec (snd p) (snd q)) as [eq2|neq2]; auto.
  - intro C. destruct H as [neq1|neq2], C as [eq1 eq2]; contradiction.
Qed.

Theorem lt_pair_alt (p q: nat * nat): lt_pair p q <-> fst p < fst q \/ (fst p = fst q /\ snd p < snd q).
Proof.
  split.
  - (* -> *) intros [[lt1 | [eq1 le2]] neq].
    + (*[ p1 < q1 ]*) left. exact lt1.
    + (*[ p1 = q1 /\ p2 <= q2 ]*) right. split; try assumption.
      apply pair_neq in neq as [neq1 | neq2].
      * contradiction.
      * apply le_neq. split; assumption.
  - (* <- *) unfold lt_pair, le_pair. intros [lt1 | [eq1 lt2]]; split.
    + left. exact lt1.
    + apply pair_neq. left. apply lt_neq. exact lt1.
    + right. apply lt_le_incl in lt2 as le2. split; assumption.
    + apply pair_neq. right. apply lt_neq. exact lt2.
Qed.

Theorem le_pair1 (p1 p2 q1 q2: nat): le_pair (p1, p2) (q1, q2) -> p1 <= q1.
Proof.
  unfold le_pair. simpl. intros [lt1 | [eq1 _]].
  - apply lt_le_incl, lt1.
  - apply eq_le_incl, eq1.
Qed.

Theorem lt_pair1 (p1 p2 q1 q2: nat): lt_pair (p1, p2) (q1, q2) -> p1 <= q1.
Proof.
  unfold lt_pair. intros [lep neq]. apply le_pair1 in lep. exact lep.
Qed.

Theorem le_pair2 (n m k: nat): le_pair (n, m) (n, k) <-> m <= k.
Proof.
  unfold le_pair. simpl. split; intro H.
  - destruct H as [lt1 | [eq1 le2]]; try assumption.
    contradict lt1. apply lt_irrefl.
  - right. split; try assumption. reflexivity.
Qed.

Theorem lt_pair2 (n m k: nat): lt_pair (n, m) (n, k) <-> m < k.
Proof.
  rewrite lt_pair_alt. simpl. split; intro H.
  - destruct H as [lt1 | [eq1 lt2]]; try assumption.
    contradict lt1. apply lt_irrefl.
  - right. split; try assumption. reflexivity.
Qed.

Theorem le_pair_zero1 (n m k: nat): le_pair (n, m) (0, k) <-> n = 0 /\ m <= k.
Proof.
  unfold le_pair. simpl. split.
  - intros [n_lt0 | [n_eq0 m_le_k]].
    + contradict n_lt0. apply nlt_0_r.
    + split; try assumption.
  - intros [n_eq0 m_le_k]. right. split; assumption.
Qed.

Theorem lt_pair_zero1 (n m k: nat): lt_pair (n, m) (0, k) <-> n = 0 /\ m < k.
Proof.
  rewrite lt_pair_alt. simpl. split; try auto.
  intros [lt0 | H]; try assumption. contradict lt0. apply nlt_0_r.
Qed.

Definition LexIH (P: nat * nat -> Prop): Prop := forall p: nat * nat, (forall q: nat * nat, lt_pair q p -> P q) -> P p.
(* P is True for left half-plane *)
Definition LHP (P: nat * nat -> Prop) (n: nat) := forall m k: nat, m <= n -> P (m, k).

Theorem lexic_induction_zero (P: nat * nat -> Prop): LexIH P -> P (0, 0).
Proof.
  intros LIH. apply LIH. intro q. rewrite (surjective_pairing q).
  rewrite lt_pair_zero1. intros [eq1 lt2].
  contradict lt2. apply nlt_0_r.
Qed.

Theorem lexic_induction_zero1' (P: nat * nat -> Prop): LexIH P -> forall n m: nat, m <= n -> P (0, m).
Proof.
  intro LIH. induction n as [|n IH].
  - intros m le0. apply le_0_r in le0 as eq0. subst m. apply lexic_induction_zero, LIH.
  - intros m le_Sn. apply le_succ_r in le_Sn. destruct le_Sn as [le_n | eq_Sn].
    + apply IH. exact le_n.
    + apply LIH. intros (n', m'). rewrite lt_pair_zero1. intros [eq_n' lt_m].
      subst n'. apply IH. apply lt_succ_r.
      apply lt_le_trans with (m := m); try assumption.
      apply eq_le_incl. exact eq_Sn.
Qed.

Theorem lexic_induction_zero1 (P: nat * nat -> Prop): LexIH P -> forall n: nat, P (0, n).
Proof. intros H n. apply (lexic_induction_zero1' P H n n). apply le_refl. Qed.

Theorem lexic_induction_step (P: nat * nat -> Prop): LexIH P -> forall n: nat, LHP P n -> LHP P (S n).
Proof.
  intros LIH n LHPn. unfold LHP. intros m k m_le_Sn.
  apply complete_induction with (P := fun x => P (m, x)).
  clear k. intros k H. destruct k as [|k].
  - apply LIH. intros (m', k). rewrite lt_pair_alt. simpl. intros [lt_m | [eq_m k_le0]].
    + apply LHPn. apply lt_succ_r, lt_le_trans with (m := m); assumption.
    + contradict k_le0. apply nlt_0_r.
  - apply le_succ_r in m_le_Sn as [m_le_n | m_eq_Sn].
    + apply LHPn. exact m_le_n.
    + subst m. apply LIH. intros (m', k'). rewrite lt_pair_alt. simpl.
      intros [m'_le_n | [m'_eq_n k'_le_k]].
      * rewrite lt_succ_r in m'_le_n. apply LHPn. exact m'_le_n.
      * subst m'. apply H. exact k'_le_k.
Qed.

Theorem lexic_induction' (P: nat * nat -> Prop): LexIH P -> forall n: nat, LHP P n.
Proof.
  intro LIH. induction n.
  + intros m k m_le0. apply le_0_r in m_le0 as m_eq0. subst m. clear m_le0.
    apply lexic_induction_zero1, LIH.
  + apply lexic_induction_step; assumption.
Qed.

Theorem lexic_induction (P: nat * nat -> Prop): LexIH P -> forall p: nat * nat, P p.
Proof. intros LIH (n, m). apply (lexic_induction' P LIH n). apply le_refl. Qed.
