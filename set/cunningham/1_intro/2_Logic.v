(** 1.2 Logical Notation *)
Require Import Setoid.
Require Import Morphisms.
From Stdlib Require Import Classical.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Bool.
From Stdlib Require Import Nat.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Strings.String.

Open Scope bool_scope.

(** some aux facts *)

Theorem negb_sym (a b: bool): negb a = b <-> a = negb b.
Proof. destruct a, b; simpl; intuition. Qed.  

Theorem contraposition (A B: Prop): (A -> B) -> (~ B -> ~ A).
Proof.
  intros HAB HnB HA. apply HnB, HAB, HA.
Qed.

Definition prop_to_bool (P: Prop): bool :=
  match (excluded_middle_informative P) with
  | left _ => true
  | right _ => false
  end.

Theorem not_in_cons {X: Type} (y x: X) (xs: list X):
  ~ In y (x :: xs) -> x <> y /\ ~ In y xs.
Proof.
  intro H. simpl in H. split.
  - intro eq. apply H. left. exact eq.
  - intro Hc. apply H. right. exact Hc.
Qed.

Theorem not_in_app {X: Type} (x: X) (xs ys: list X):
  ~ In x (xs ++ ys) -> ~ In x xs /\ ~ In x ys.
Proof.
  intro H. split; intro C; apply H; apply in_or_app.
  - left. exact C.
  - right. exact C.
Qed.

(** Propositions and Logical Connectives *)
(* boolean statement *)
Inductive St :=
| StConst (b: bool)
| StVar (name: string)
| StNot: St -> St
| StAnd: St -> St -> St
| StOr: St -> St -> St
| StImpl: St -> St -> St
| StIff: St -> St -> St.


(* Notations *)
Open Scope string_scope.

Definition T: bool := true.
Definition F: bool := false.
Definition bvals := [F; T].

Definition P: string := "P".
Definition Q: string := "Q".
Definition R: string := "R".

(* see https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html#lab403 for details *)
Coercion StVar : string >-> St.
Coercion StConst : bool >-> St.

Declare Custom Entry st.
Declare Scope st_scope.

Notation "<{ s }>" := s (s custom st).
Notation "( x )" := x (in custom st, x at level 99).
Notation "x" := x (in custom st at level 0, x constr at level 0).
Notation "x -> y" := (StImpl x y) (in custom st at level 95, right associativity).
Notation "x <-> y" := (StIff x y) (in custom st at level 90, right associativity).
Notation "x | y" := (StOr x y) (in custom st at level 85, right associativity).
Notation "x & y" := (StAnd x y) (in custom st at level 80, right associativity).
Notation "'~' b" := (StNot b) (in custom st at level 75, right associativity).
Notation "'T'" := (StConst T) (in custom st at level 0).
Notation "'F'" := (StConst F) (in custom st at level 0).
Notation "'P'" := (StVar P) (in custom st at level 0).
Notation "'Q'" := (StVar Q) (in custom st at level 0).

Check <{ ~ P  -> Q }>.
Check <{ ~(P & Q | P) <-> ~P | F }>.
Unset Printing Notations.
Check <{ ~(P & Q | P) <-> ~P | F }>.
Set Printing Notations.

(** String Map *)
Definition SMap (X: Type) := string -> X.
Definition SMap_default {X: Type} (x: X): SMap X := fun _ => x.
Definition SMap_update {X: Type} (m: SMap X) (k: string) (x: X): SMap X :=
  fun s => if s =? k then x else m s.

Notation "'_' '!->' x" := (SMap_default x) (at level 100, right associativity).
Notation "k '!->' x ';' m" :=
  (SMap_update m k x) (at level 100, k constr, right associativity).

Theorem SMap_update_eq {X: Type} (k: string) (x: X) (m: SMap X):
  (k !-> x; m) k = x.
Proof. unfold SMap_update. rewrite eqb_refl. reflexivity. Qed.

Theorem SMap_update_neq {X: Type} (k x: string) (v: X) (m: SMap X):
  k <> x -> (k !-> v; m) x = m x.
Proof.
  unfold SMap_update. intro neq.
  apply eqb_neq in neq. rewrite eqb_sym. rewrite neq. reflexivity.
Qed.

Definition SMap_map {X Y: Type} (f: X -> Y) (m: SMap X): SMap Y := fun k => f (m k).

Definition SMap_map_bool_prop := SMap_map is_true.
Definition SMap_map_prop_bool := SMap_map prop_to_bool.

(* map pointwise equality *)
Definition EqM {X: Type} (m n: SMap X) := forall x, m x = n x.
Notation "m == n" := (EqM m n) (at level 70, no associativity).

Instance EqM_refl {X: Type}: Reflexive (@EqM X).
Proof. unfold Reflexive, EqM. reflexivity. Qed.

Instance EqM_sym {X: Type}: Symmetric (@EqM X).
Proof. unfold Symmetric, EqM. auto. Qed.

Instance EqM_trans {X: Type}: Transitive (@EqM X).
Proof.
  unfold Transitive, EqM.
  intros m n p H1 H2 x. rewrite H1, H2. reflexivity.
Qed.

Instance EqM_equiv {X: Type}: Equivalence (@EqM X).
Proof.
  split. 
  - apply EqM_refl.
  - apply EqM_sym.
  - apply EqM_trans.
Qed.

Theorem SMap_update_same {X: Type} (m: SMap X) (k: string):
  (k !-> m k; m) == m.
Proof.
  intro x. unfold SMap_update. destruct (eqb_spec x k) as [eq|neq].
  - subst x. reflexivity.
  - reflexivity.
Qed.

Theorem SMap_same_update {X: Type} (m: SMap X) (k: string) (u v: X):
  (k !-> v; k !-> u; m) == (k !-> v; m).
Proof.
  intro x. unfold SMap_update.
  destruct (eqb_spec x k) as [eq|neq]; reflexivity.
Qed.

Instance EqM_update_proper {X: Type}:
  Proper (EqM ==> eq ==> eq ==> EqM) (@SMap_update X).
Proof.
  unfold Proper, respectful.
  intros m n eq_mn u v eq_uv x y eq_xy k. subst y u.
  unfold SMap_update. destruct (eqb_spec k v) as [eq_kv|neq_kv].
  - reflexivity.
  - apply eq_mn.
Qed.

Theorem SMap_update_inj {X: Type} (k: string) (v: X) (m n: SMap X):
  m == n -> (k !-> v; m) == (k !-> v; n).
Proof. intro eq. rewrite eq. reflexivity. Qed.

Theorem SMap_update_reorder {X: Type} (k1 k2: string) (v1 v2: X) (m: SMap X):
  k1 <> k2 -> (k1 !-> v1; k2 !-> v2; m) == (k2 !-> v2; k1 !-> v1; m).
Proof.
  intros neq x. unfold SMap_update.
  destruct (eqb_spec x k1) as [eq1|neq1], (eqb_spec x k2) as [eq2|neq2];
    try reflexivity.
  contradict eq2. subst x. exact neq.
Qed.

Definition PQ_vals: list (SMap bool) :=
  map (fun '(p, q) => (P !-> p; Q !-> q; _ !-> F)) (list_prod bvals bvals).

(** eval *)
Fixpoint eval (m: SMap bool) (s: St): bool :=
  match s with
  | StConst b => b
  | StVar name => m name
  | StNot x => negb (eval m x)
  | StAnd x y => (eval m x) && (eval m y)
  | StOr x y => (eval m x) || (eval m y)
  | StImpl x y => implb (eval m x) (eval m y)
  | StIff x y => Bool.eqb (eval m x) (eval m y)
  end.

Fixpoint eval_prop (m: SMap Prop) (s: St): Prop :=
  match s with
  | StConst b => is_true b
  | StVar name => m name
  | StNot x => ~(eval_prop m x)
  | StAnd x y => (eval_prop m x) /\ (eval_prop m y)
  | StOr x y => (eval_prop m x) \/ (eval_prop m y)
  | StImpl x y => (eval_prop m x) -> (eval_prop m y)
  | StIff x y => (eval_prop m x) <-> (eval_prop m y)
  end.

(* Problem 1. Construct a truth table for the sentence ¬ P → (Q ∧ P) *)
Definition pr1 := <{ ~P -> Q & P }>.
Compute map (fun m => (m P, m Q, eval m pr1)) PQ_vals.

Example pr1_is_p (m: SMap bool): eval m pr1 = eval m P.
Proof. simpl. destruct (m P), (m Q); reflexivity. Qed.

Instance EqM_eval_proper: Proper (EqM ==> eq ==> eq) eval.
Proof.
  unfold Proper, respectful.
  intros x y H s t eq. subst t.
  generalize dependent y.
  generalize dependent x.
  induction s; intros x y H; simpl.
  - reflexivity.
  - apply H.
  - rewrite (IHs x y) by exact H. reflexivity.
  - rewrite (IHs1 x y), (IHs2 x y) by exact H. reflexivity.
  - rewrite (IHs1 x y), (IHs2 x y) by exact H. reflexivity.
  - rewrite (IHs1 x y), (IHs2 x y) by exact H. reflexivity.
  - rewrite (IHs1 x y), (IHs2 x y) by exact H. reflexivity.
Qed.

Theorem eval_impl_eval_prop (s: St) (mb: SMap bool):
  eval mb s = true <-> eval_prop (SMap_map_bool_prop mb) s.
Proof.
  generalize dependent mb.
  induction s; simpl; intro mb; split; intro H; try apply H.
  - rewrite <- IHs. apply eq_true_not_negb_iff. exact H.
  - rewrite <- IHs in H. apply eq_true_not_negb_iff. exact H.
  - rewrite <- IHs1, <- IHs2. apply andb_prop. exact H.
  - rewrite <- IHs1, <- IHs2 in H. apply andb_true_intro. exact H.
  - rewrite <- IHs1, <- IHs2. apply orb_prop. exact H.
  - rewrite <- IHs1, <- IHs2 in H. apply orb_true_intro. exact H.
  - rewrite <- IHs1, <- IHs2. apply implb_true_iff. exact H.
  - rewrite <- IHs1, <- IHs2 in H. apply implb_true_iff. exact H.
  - rewrite <- IHs1, <- IHs2. apply eqb_prop in H. rewrite H. reflexivity.
  - rewrite <- IHs1, <- IHs2 in H. apply eq_iff_eq_true in H.
    rewrite <- H. apply eqb_reflx.
Qed.

Theorem eval_prop_impl_eval (s: St) (mp: SMap Prop):
  eval_prop mp s <-> eval (SMap_map_prop_bool mp) s = true.
Proof.
  unfold SMap_map_prop_bool, SMap_map, prop_to_bool.
  generalize dependent mp.
  induction s; simpl; intro mp; split; intro H; try apply H.
  - destruct (excluded_middle_informative (mp name)) as [HT | HF].
    + reflexivity.
    + contradiction.
  - destruct (excluded_middle_informative (mp name)) as [HT | HF].
    + assumption.
    + discriminate.
  - apply eq_true_not_negb_iff. rewrite IHs in H. exact H.
  - rewrite IHs. apply eq_true_not_negb_iff. exact H.
  - rewrite IHs1, IHs2 in H. apply andb_true_intro. exact H.
  - rewrite IHs1, IHs2. apply andb_prop. exact H.
  - rewrite IHs1, IHs2 in H. apply orb_true_intro. exact H.
  - rewrite IHs1, IHs2. apply orb_prop. exact H.
  - rewrite IHs1, IHs2 in H. apply implb_true_iff. exact H.
  - rewrite IHs1, IHs2. apply implb_true_iff. exact H.
  - rewrite IHs1, IHs2 in H. apply eq_iff_eq_true in H.
    rewrite <- H. apply eqb_reflx.
  - rewrite IHs1, IHs2. apply eq_iff_eq_true.
    apply eqb_prop in H. rewrite H. reflexivity.
Qed.

Definition ConstB (b: bool) (s: St): Prop := forall m, eval m s = b.

(** Definition 1.2.1. *)
Definition TautologyB := ConstB true.

Definition TautologyP (s: St) := forall m, eval_prop m s.

Theorem LEMB: TautologyB <{ P | ~P }>.
Proof. intros m. simpl. destruct (m P); reflexivity. Qed.

Example LEMP: TautologyP <{ P | ~P }>.
Proof. intros m. simpl. destruct (classic (m P)); auto. Qed.

Theorem TautologyP_iff_B (s: St): TautologyP s <-> TautologyB s.
Proof.
  unfold TautologyB, ConstB, TautologyP.
  split; intros H m.
  - apply eval_impl_eval_prop. apply H.
  - apply eval_prop_impl_eval. apply H.
Qed.

(** Definition 1.2.2. *)
Definition ContradictionB := ConstB false.

Definition ContradictionP (s: St) := forall m, ~ eval_prop m s.

Theorem ContradictionAndB': ContradictionB <{ P & ~P }>.
Proof. intros m. simpl. destruct (m P); reflexivity. Qed.

Theorem ContradictionAnd: ContradictionP <{ P & ~P }>.
Proof.
  intros m. simpl. remember (m P) as H eqn:eq. intuition.
Qed.

(** LogicalEquivalence *)

(** Definition 1.2.3.
    [P(X)] and [Q(X)] are logically equivalent (P <=> Q) iff [forall X, P X = Q X] *)
Definition EqB (p q: St) := forall m, eval m p = eval m q.
Notation "p '<=>' q" := (EqB p q) (at level 70, no associativity).
Notation "p '</=>' q" := (~(EqB p q)) (at level 70, no associativity).

(* implement ideas from https://www.cis.upenn.edu/~plclub/blog/2020-05-15-Rewriting-in-Coq/ *)
Instance EqB_refl: Reflexive EqB.
Proof. unfold Reflexive, EqB. reflexivity. Qed.

Instance EqB_sym: Symmetric EqB.
Proof. unfold Symmetric, EqB. auto. Qed.

Instance EqB_trans: Transitive EqB.
Proof.
  unfold Transitive, EqB.
  intros p q r H1 H2 m. rewrite H1, H2. reflexivity.
Qed.

Instance EqB_equiv: Equivalence EqB.
Proof.
  split. 
  - apply EqB_refl.
  - apply EqB_sym.
  - apply EqB_trans.
Qed.

Instance EqB_not_proper: Proper (EqB ==> EqB) StNot.
Proof.
  unfold Proper, respectful.
  intros p q H m. simpl. rewrite H. reflexivity.
Qed.

Example StNot_rewrite_ex (p q: St): p <=> q -> <{ ~p }> <=> <{ ~q }>.
Proof. intro H. rewrite H. reflexivity. Qed.

Instance EqB_and_proper: Proper (EqB ==> EqB ==> EqB) StAnd.
Proof.
  unfold Proper, respectful, EqB.
  intros p1 q1 H1 p2 q2 H2 m. simpl. rewrite H1, H2. reflexivity.
Qed.

Instance EqB_or_proper: Proper (EqB ==> EqB ==> EqB) StOr.
Proof.
  unfold Proper, respectful, EqB.
  intros p1 q1 H1 p2 q2 H2 m. simpl. rewrite H1, H2. reflexivity.
Qed.

Instance EqB_impl_proper: Proper (EqB ==> EqB ==> EqB) StImpl.
Proof.
  unfold Proper, respectful, EqB.
  intros p1 q1 H1 p2 q2 H2 m. simpl. rewrite H1, H2. reflexivity.
Qed.

Instance EqB_iff_proper: Proper (EqB ==> EqB ==> EqB) StIff.
Proof.
  unfold Proper, respectful, EqB.
  intros p1 q1 H1 p2 q2 H2 m. simpl. rewrite H1, H2. reflexivity.
Qed.

Theorem TautologyB_prop (s: St): TautologyB s <-> (s <=> true).
Proof.
  unfold TautologyB, ConstB, EqB. simpl. reflexivity.
Qed.

Theorem ContradictionB_prop (s: St): ContradictionB s <-> (s <=> false).
Proof.
  unfold ContradictionB, ConstB, EqB. simpl. reflexivity.
Qed.

(* De Morgan’s Laws *)
Theorem DMLB1 (p q: St): <{ ~(p | q) }> <=> <{ ~p & ~q }>.
Proof.
  unfold EqB. intro m. simpl.
  destruct (eval m p), (eval m q); reflexivity.
Qed.

Theorem DMLB1': <{ ~(P | Q) }> <=> <{ ~P & ~Q }>.
Proof.
  unfold EqB. intro m. simpl.
  destruct (m P), (m Q); reflexivity.
Qed.

Theorem DML1 (P Q: Prop): ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
  split; intro H.
  - split; intro C; apply H.
    + left. exact C.
    + right. exact C.
  - destruct H as [HnP HnQ]. intros [C | C]; auto.
Qed.

Theorem DMLB2 (p q: St): <{ ~(p & q) }> <=> <{ ~p | ~q }>.
Proof.
  unfold EqB. intro m. simpl.
  destruct (eval m p), (eval m q); reflexivity.
Qed.

Theorem DML2 (P Q: Prop): ~(P /\ Q) <-> ~P \/ ~Q.
Proof.
  split; intro H.
  - destruct (classic P) as [HP | HnP].
    + right. auto.
    + left. exact HnP.
  - intros [HP HQ]. destruct H; contradiction.
Qed.

Example apply_DML2: <{ ~((P -> Q) & (Q -> P)) }> <=> <{ ~(P -> Q) | ~(Q -> P) }>.
Proof. rewrite DMLB2. reflexivity. Qed.

(* Problem 3. Show that sentences P ∨ (Q ∧ ¬P) and (P ∨ Q) ∧ ¬P
   are not logically equivalent.*)
Example EqB_neg_ex: <{ P | (Q & ~P) }> </=> <{ (P | Q) & ~P }>.
Proof.
  unfold EqB. intros H.
  pose (H (P !-> T; _ !-> F)) as C. simpl in C.
  discriminate C.
Qed.

(* Propositional Logic Laws *)

Section StSubstitution.

(* substitute all instances of [StVar k] in [p] by [r] *)
Fixpoint St_subst (k: string) (r p: St): St :=
  match p with
  | StConst _ as x => x
  | StVar name as x => if name =? k then r else x
  | StNot x => StNot (St_subst k r x)
  | StAnd x y => StAnd (St_subst k r x) (St_subst k r y)
  | StOr x y => StOr (St_subst k r x) (St_subst k r y)
  | StImpl x y => StImpl (St_subst k r x) (St_subst k r y)
  | StIff x y => StIff (St_subst k r x) (St_subst k r y)
  end.

Theorem all_eval_andb_true_iff (s t: St):
  (forall m, eval m s && eval m t = true) <->
    (forall m, eval m s = true) /\ (forall m, eval m t = true).
Proof.
  split; intro H.
  - split; intro m.
    + pose (H m) as Hm. apply andb_true_iff in Hm as [H1 H2]. exact H1.
    + pose (H m) as Hm. apply andb_true_iff in Hm as [H1 H2]. exact H2.
  - intro m. destruct H as [H1 H2].
    rewrite H1, H2. reflexivity.
Qed.

Theorem all_eval_andb_false_iff (s t: St):
  (forall m, eval m s && eval m t = false) <->
    (forall m, eval m s = false \/ eval m t = false).
Proof.
  split; intros H m; pose (H m) as Hm.
  - apply andb_false_iff in Hm.
    destruct Hm as [H1 | H2]; auto.
  - apply andb_false_iff. exact Hm.
Qed.

Theorem St_subst_prop (k: string) (s r: St) (m: SMap bool):
  eval m (St_subst k r s) = eval (k !-> eval m r; m) s.
Proof.
  generalize dependent m.
  induction s as [b | v | s IH | s1 IH1 s2 IH2
                 | s1 IH1 s2 IH2 | s1 IH1 s2 IH2 | s1 IH1 s2 IH2];
    intro m.
  - (* s = StConst b *) reflexivity.
  - (* s = StVar v *) simpl. destruct (v =? k) eqn:eq.
    + (* v = k *) apply eqb_eq in eq. rewrite eq, SMap_update_eq. reflexivity.
    + (* v <> k *) unfold SMap_update. rewrite eq. reflexivity.
  - (* s = StNot *) simpl. pose (IH m) as H. rewrite H. reflexivity.
  - (* s = StAnd *) simpl. rewrite IH1, IH2. reflexivity.
  - (* s = StOr *) simpl. rewrite IH1, IH2. reflexivity.
  - (* s = StImpl *) simpl. rewrite IH1, IH2. reflexivity.
  - (* s = StIff *) simpl. rewrite IH1, IH2. reflexivity.
Qed.

Theorem St_subst_in_const (b: bool) (k: string) (s r: St):
  (forall m, eval m s = b) -> (forall n, eval n (St_subst k r s) = b).
Proof.
  intros H n.
  pose (St_subst_prop k s r n) as E.
  rewrite E. apply H.
Qed.

Instance EqB_subst_proper (k: string) (r: St): Proper (EqB ==> EqB) (St_subst k r).
Proof.
  unfold Proper, respectful, EqB. intros p q H m.
  rewrite !St_subst_prop. rewrite H. reflexivity.
Qed.

Theorem EqB_subst (k: string) (r p q: St):
  p <=> q -> St_subst k r p <=> St_subst k r q.
Proof.
  intro H. rewrite H. reflexivity.
Qed.

Theorem eval_eq (m n: SMap bool) (s t: St):
  s <=> t -> m == n -> eval m s = eval n t.
Proof.
  intros eq_st eq_ev.
  rewrite eq_ev. apply eq_st.
Qed.

Theorem ContradictionAndB (p: St): ContradictionB <{ p & ~p }>.
Proof.
  pose ContradictionAndB' as H. rewrite ContradictionB_prop in H.
  apply (EqB_subst P p) in H. simpl in H. apply ContradictionB_prop.
  exact H.
Qed.

(** rename to avoid collisins *)
(* fresh_str *)
Fixpoint longest_str (x: string) (xs: list string): string :=
  match xs with
  | [] => x
  | y :: ys => if Nat.ltb (length x) (length y)
             then longest_str y ys
             else longest_str x ys
  end.

Lemma longest_str_head (x: string) (xs: list string):
  length x <= length (longest_str x xs).
Proof.
  generalize dependent x.
  induction xs as [| y xs IH]; intro x.
  { simpl. apply le_n. }
  simpl. destruct (length x <? length y)%nat eqn:H.
  - apply PeanoNat.Nat.ltb_lt in H. apply PeanoNat.Nat.lt_le_incl.
    apply PeanoNat.Nat.lt_le_trans with (length y).
    { exact H. } apply IH.
  - apply IH.
Qed.

Lemma longest_str_tail (x y: string) (xs: list string):
  In y xs -> length y <= length (longest_str x xs).
Proof.
  generalize dependent y.
  generalize dependent x.
  induction xs as [| z xs IH]; intros x y H. { inversion H. }
  simpl in H. destruct H as [H | H].
  - subst z. simpl. destruct (length x <? length y)%nat eqn:H1.
    { apply longest_str_head. }
    apply PeanoNat.Nat.ltb_ge in H1.
    apply PeanoNat.Nat.le_trans with (length x). { exact H1. }
    apply longest_str_head.
  - simpl. destruct (length x <? length z)%nat eqn:H1.
    + apply IH. apply H.
    + apply IH. apply H.
Qed.

Theorem longest_str_prop (x: string) (xs: list string):
  forall y: string, In y (x :: xs) -> length y <= length (longest_str x xs).
Proof.
  intros y [H | H].
  - subst y. apply longest_str_head.
  - apply longest_str_tail. apply H.
Qed.

Definition fresh_str (xs: list string): string :=
  match xs with
  | [] => ""
  | x :: xs => String "x"%char (longest_str x xs)
  end.

Theorem fresh_str_longer (x: string) (xs: list string):
  let f := fresh_str (x :: xs)
  in length (longest_str x xs) < length f.
Proof. simpl. apply PeanoNat.Nat.lt_succ_diag_r. Qed.

Theorem fresh_str_longest (xs: list string):
  forall y: string, In y xs -> length y < length (fresh_str xs).
Proof.
  intros y H. destruct xs as [| x xs]. { inversion H. }
  apply PeanoNat.Nat.le_lt_trans with (length (longest_str x xs)).
  - apply longest_str_prop. apply H.
  - apply fresh_str_longer.
Qed.

Theorem fresh_str_fresh (xs: list string): ~ In (fresh_str xs) xs.
Proof.
  intro H. apply fresh_str_longest in H.
  apply (PeanoNat.Nat.lt_irrefl _ H).
Qed.

Theorem fresh_str_cons_fresh_head (x: string) (xs: list string):
  x <> fresh_str (x :: xs).
Proof.
  pose (fresh_str_longer x xs) as H1. intro H.
  rewrite <- H in H1. simpl in H1.
  assert (length x <= length (longest_str x xs)) as H2.
  { apply longest_str_prop. apply in_eq. }
  assert (length x < length x) as C.
  { apply PeanoNat.Nat.le_lt_trans with (length (longest_str x xs)).
    - exact H2.
    - exact H1. }
  apply (PeanoNat.Nat.lt_irrefl (length x)). exact C.
Qed.  

Theorem fresh_str_cons_fresh_tail (x: string) (xs: list string):
  ~ In (fresh_str (x :: xs)) xs.
Proof.
  intro H. apply fresh_str_fresh with (x :: xs).
  remember (fresh_str (x :: xs)) as f eqn:eq.
  apply in_cons. exact H.
Qed.

Theorem fresh_str_cons_prop (f x: string) (xs: list string):
  f = fresh_str (x :: xs) -> x <> f /\ ~ In f xs.
Proof.
  intro H. subst f. split.
  - apply fresh_str_cons_fresh_head.
  - apply fresh_str_cons_fresh_tail.
Qed.

Theorem fresh_str_app_l_fresh (xs ys: list string):
  ~ In (fresh_str (xs ++ ys)) xs.
Proof.
  induction xs as [| x xs IH]. { auto. }
  simpl. intros [H | H].
  { apply (fresh_str_cons_fresh_head x (xs ++ ys) H). }
  apply (fresh_str_cons_fresh_tail x (xs ++ ys)). simpl.
  apply in_or_app. left. exact H.
Qed.

Theorem fresh_str_app_r_fresh (xs ys: list string):
  ~ In (fresh_str (xs ++ ys)) ys.
Proof.
  induction xs as [| x xs IH]. { simpl. apply fresh_str_fresh. }
  simpl. intros H. apply (fresh_str_cons_fresh_tail x (xs ++ ys)). simpl.
  apply in_or_app. right. exact H.
Qed.

Theorem fresh_str_app_prop (f: string) (xs ys: list string):
  f = fresh_str (xs ++ ys) -> ~ In f xs /\ ~ In f ys.
Proof.
  intro H. subst f. split.
  - apply fresh_str_app_l_fresh.
  - apply fresh_str_app_r_fresh.
Qed.

(* list vars *)
Fixpoint list_vars (s: St): list string :=
  match s with
  | StConst b => []
  | StVar v => [v]
  | StNot x => list_vars x
  | StAnd x y => list_vars x ++ list_vars y
  | StOr x y => list_vars x ++ list_vars y
  | StImpl x y => list_vars x ++ list_vars y
  | StIff x y => list_vars x ++ list_vars y
  end.

Fixpoint StIn (x: string) (s: St): Prop :=
  match s with
  | StConst b => False
  | StVar v => x = v
  | StNot t => StIn x t
  | StAnd t u => StIn x t \/ StIn x u
  | StOr t u => StIn x t \/ StIn x u
  | StImpl t u => StIn x t \/ StIn x u
  | StIff t u => StIn x t \/ StIn x u
  end.

Theorem StIn_prop (x: string) (s: St): StIn x s <-> In x (list_vars s).
Proof.
  induction s; simpl; intuition.
  - apply in_app_or in H3 as [H3 | H3]; intuition.
  - apply in_app_or in H3 as [H3 | H3]; intuition.
  - apply in_app_or in H3 as [H3 | H3]; intuition.
  - apply in_app_or in H3 as [H3 | H3]; intuition.
Qed.

Theorem fresh_str_not_In_St (s: St): ~ StIn (fresh_str (list_vars s)) s.
Proof. rewrite StIn_prop. apply fresh_str_fresh. Qed.

Theorem eval_fresh (m: SMap bool) (k: string) (v: bool) (s: St):
  ~ StIn k s -> eval (k !-> v; m) s = eval m s.
Proof.
  induction s; simpl; intro Hf.
  - reflexivity.
  - apply eqb_neq in Hf. unfold SMap_update.
    rewrite eqb_sym, Hf. reflexivity.
  - apply IHs in Hf as IH. rewrite IH. reflexivity.
  - apply DML1 in Hf as [H1 H2]. rewrite (IHs1 H1), (IHs2 H2). reflexivity.
  - apply DML1 in Hf as [H1 H2]. rewrite (IHs1 H1), (IHs2 H2). reflexivity.
  - apply DML1 in Hf as [H1 H2]. rewrite (IHs1 H1), (IHs2 H2). reflexivity.
  - apply DML1 in Hf as [H1 H2]. rewrite (IHs1 H1), (IHs2 H2). reflexivity.
Qed.

(* rename all StVar's with name = u to v *)
Definition St_rename (u v: string) (s: St) := St_subst u (StVar v) s.

Theorem St_rename_id (k: string) (s: St): St_rename k k s = s.
Proof.
  induction s; unfold St_rename in * |- *; simpl.
  - reflexivity.
  - destruct (eqb_spec name k) as [eq|neq].
    + simpl. subst k. reflexivity.
    + simpl. reflexivity.
  - rewrite IHs. reflexivity.
  - rewrite IHs1, IHs2; try assumption. reflexivity.
  - rewrite IHs1, IHs2; try assumption. reflexivity.
  - rewrite IHs1, IHs2; try assumption. reflexivity.
  - rewrite IHs1, IHs2; try assumption. reflexivity.
Qed.

Theorem St_rename_equiv_back (u v: string) (s: St) (m: SMap bool):
  eval m (St_rename u v s) = eval (u !-> m v; m) s.
Proof. unfold St_rename. apply St_subst_prop. Qed.

Theorem St_rename_involutive (u v: string) (s: St):
  ~ StIn v s -> s = St_rename v u (St_rename u v s).
Proof.
  unfold St_rename. induction s; simpl; intro Hn.
  - reflexivity.
  - destruct (eqb_spec name u) as [eq|neq].
    + simpl. rewrite eqb_refl. subst u. reflexivity.
    + simpl. apply eqb_neq in Hn. rewrite eqb_sym. rewrite Hn. reflexivity.
  - rewrite <- IHs. { reflexivity. } exact Hn.
  - apply not_or_and in Hn. destruct Hn as [H1 H2].
    rewrite <- IHs1, <- IHs2; try assumption. reflexivity.
  - apply not_or_and in Hn. destruct Hn as [H1 H2].
    rewrite <- IHs1, <- IHs2; try assumption. reflexivity.
  - apply not_or_and in Hn. destruct Hn as [H1 H2].
    rewrite <- IHs1, <- IHs2; try assumption. reflexivity.
  - apply not_or_and in Hn. destruct Hn as [H1 H2].
    rewrite <- IHs1, <- IHs2; try assumption. reflexivity.
Qed.

Theorem St_rename_equiv (u v: string) (s: St) (m: SMap bool):
  ~ StIn v s -> eval m s = eval (v !-> m u; m) (St_rename u v s).
Proof.
  intro Hn. rewrite (St_rename_involutive u v s Hn) at 1.
  apply St_rename_equiv_back.
Qed.  

Theorem St_rename_fresh (m: SMap bool) (k f: string) (s: St) (v: bool):
  ~ StIn f s -> eval m (St_rename k f s) = eval (k !-> v; m) (St_rename k f s).
Proof.
  intro Hf. unfold St_rename. rewrite !St_subst_prop.
  simpl. destruct (eqb_spec k f) as [eq|neq].
  - subst f. rewrite SMap_update_eq.
    rewrite !(eval_fresh _ k _ s Hf). reflexivity.
  - rewrite (SMap_update_neq k f v m neq).
    rewrite SMap_same_update. reflexivity.
Qed.

Theorem St_subst_fresh (f: string) (r s: St): ~ StIn f s -> St_subst f r s = s.
Proof.
  induction s; simpl; intro nin; try rewrite IHs1, IHs2; auto.
  - destruct (eqb_spec name f) as [eq|neq].
    + subst name. contradiction nin. reflexivity.
    + reflexivity.
  - rewrite IHs; auto.
Qed.

Theorem StIn_rename (f k: string) (s: St):
  StIn k (St_rename k f s) -> StIn k s /\ f = k.
Proof.
  unfold St_rename. induction s; simpl; intro H; intuition;
    destruct (eqb_spec name k) as [eq|neq]; simpl in H.
  - subst name f. reflexivity.
  - subst name. contradict neq. reflexivity.
  - subst name f. reflexivity.
  - subst name. contradict neq. reflexivity.
Qed.

Theorem St_not_in_fresh_rename (f k: string) (s: St):
  ~ StIn f s -> ~ StIn k (St_rename k f s).
Proof.
  intros C H. apply StIn_rename in H as [H eq].
  subst f. apply C, H.
Qed.

Theorem St_subst_after_fresh_rename (f k: string) (r s: St):
  ~ StIn f s -> St_subst k r (St_rename k f s) = St_rename k f s.
Proof.
  intro H. apply St_subst_fresh. apply St_not_in_fresh_rename, H.
Qed.

Theorem St_subst_with_fresh_rename (f k: string) (r s: St):
  ~ StIn f s -> St_subst f r (St_rename k f s) = St_subst k r s.
Proof.
  unfold St_rename. induction s; simpl; intro H;
    try rewrite IHs1, IHs2; auto.
  - destruct (eqb_spec name k) as [eq|neq]; simpl.
    + rewrite eqb_refl. reflexivity.
    + apply eqb_neq in H. rewrite eqb_sym. rewrite H. reflexivity.
  - rewrite (IHs H). reflexivity.
Qed.

Theorem St_subst_fresh_reorder (k1 k2: string) (r1 r2 s: St):
  k1 <> k2 -> ~ StIn k1 r2 -> ~ StIn k2 r1
  -> St_subst k1 r1 (St_subst k2 r2 s) = St_subst k2 r2 (St_subst k1 r1 s).
Proof.
  induction s; simpl; intros neq H1 H2.
  - reflexivity.
  - destruct (eqb_spec name k1) as [eq1 | neq1];
      destruct (eqb_spec name k2) as [eq2 | neq2]; simpl.
    + subst k2 name. contradict neq. reflexivity.
    + subst name. rewrite eqb_refl.
      rewrite St_subst_fresh; [ reflexivity | exact H2 ].
    + subst name. rewrite eqb_refl.
      rewrite St_subst_fresh; [ reflexivity | exact H1 ].
    + apply eqb_neq in neq1. apply eqb_neq in neq2.
      rewrite neq1, neq2. reflexivity.
  - rewrite IHs; auto.
  - rewrite IHs1, IHs2; auto.
  - rewrite IHs1, IHs2; auto.
  - rewrite IHs1, IHs2; auto.
  - rewrite IHs1, IHs2; auto.
Qed.

Definition St_subst2 (k1: string) (r1: St) (k2: string) (r2 s: St): St :=
  let f := fresh_str (k1 :: k2 :: (list_vars r1) ++ (list_vars r2) ++ (list_vars s)) in
  let r1' := St_rename k2 f r1 in
  let s1 := St_subst k1 r1' s in
  let s2 := St_subst k2 r2 s1
  in St_rename f k2 s2.

Instance EqB_subst2_proper (k1: string) (r1: St) (k2: string) (r2: St):
  Proper (EqB ==> EqB) (St_subst2 k1 r1 k2 r2).
Proof.
  unfold Proper, respectful, EqB, St_subst2. intros p q H m.
  remember (fresh_str (k1 :: k2 :: list_vars r1 ++ list_vars r2 ++ list_vars p))
    as fp eqn:eq_fp.
  remember (fresh_str (k1 :: k2 :: list_vars r1 ++ list_vars r2 ++ list_vars q))
    as fq eqn:eq_fq.
  rewrite !St_rename_equiv_back. rewrite !St_subst_prop.
  remember (fp !-> m k2; m) as mp eqn:eq_mp.
  remember (fq !-> m k2; m) as mq eqn:eq_mq.
  pose (fresh_str_cons_prop fp k1 _ eq_fp) as Hp.
  destruct Hp as [neq_fp_k1 Hp]. apply not_in_cons in Hp as [neq_fp_k2 Hp].
  apply not_in_app in Hp as [Hpr1 Hp]. apply not_in_app in Hp as [Hpr2 Hp].
  pose (fresh_str_cons_prop fq k1 _ eq_fq) as Hq.
  destruct Hq as [neq_fq_k1 Hq]. apply not_in_cons in Hq as [neq_fq_k2 Hq].
  apply not_in_app in Hq as [Hqr1 Hq]. apply not_in_app in Hq as [Hqr2 Hq].
  rewrite <- StIn_prop in Hpr1, Hpr2, Hp, Hqr1, Hqr2, Hq.
  rewrite <- !St_rename_fresh by assumption.
  rewrite eq_mp at 3. rewrite <- St_rename_equiv by assumption.
  rewrite eq_mq at 3. rewrite <- St_rename_equiv by assumption.
  subst mp mq.
  rewrite (eval_fresh m fp), (eval_fresh m fq) by assumption.
  rewrite (SMap_update_reorder k2 fp), (SMap_update_reorder k1 fp) by assumption.
  rewrite (eval_fresh _ fp) by assumption.
  rewrite (SMap_update_reorder k2 fq), (SMap_update_reorder k1 fq) by assumption.
  rewrite (eval_fresh _ fq) by assumption.
  rewrite H. reflexivity.
Qed.

Theorem EqB_subst2 (k1: string) (r1: St) (k2: string) (r2 p q: St):
  p <=> q -> St_subst2 k1 r1 k2 r2 p <=> St_subst2 k1 r1 k2 r2 q.
Proof.
  intro H. rewrite H. reflexivity.
Qed.

Theorem DMLB1_ex (p q: St): <{ ~(p | q) }> <=> <{ ~p & ~q }>.
Proof.
  pose DMLB1' as H.
  apply (EqB_subst2 P p Q q) in H. unfold St_subst2 in H. simpl in H.
  remember (String "x" (longest_str P (list_vars p ++ list_vars q ++ [P; Q])))
    as f eqn:eq_f.
  assert (f = fresh_str (P :: Q :: list_vars p ++ list_vars q ++ [P; Q])) as eq_f'.
  { simpl. exact eq_f. }
  pose (fresh_str_cons_prop f _ _ eq_f') as nin. destruct nin as [neq_fp nin].
  apply not_in_cons in nin as [neq_fq nin].
  apply not_in_app in nin as [nin_p nin]. apply not_in_app in nin as [nin_q _].
  rewrite <- StIn_prop in nin_p, nin_q.
  rewrite St_subst_after_fresh_rename in H by assumption.
  unfold St_rename in H. simpl in H. fold (St_rename Q f p) in H.
  rewrite St_subst_with_fresh_rename in H by assumption.
  fold (St_rename Q Q p) in H.
  rewrite St_rename_id in H.
  rewrite St_subst_fresh in H by assumption. exact H.
Qed.

End StSubstitution.

(** Other Laws *)

Theorem AndB_comm (a b: St): <{ a & b }> <=> <{ b & a }>.
Proof. intro m. simpl. apply andb_comm. Qed.

Theorem OrB_comm (a b: St): <{ a | b }> <=> <{ b | a }>.
Proof. intro m. simpl. apply orb_comm. Qed.

Theorem AndB_assoc (a b c: St): <{ a & (b & c) }> <=> <{ (a & b) & c }>.
Proof. intro m. simpl. apply andb_assoc. Qed.

Theorem OrB_assoc (a b c: St): <{ a | (b | c) }> <=> <{ (a | b) | c }>.
Proof. intro m. simpl. apply orb_assoc. Qed.

Theorem AndB_idempotent (a: St): <{ a & a }> <=> a.
Proof. intro m. simpl. apply andb_diag. Qed.

Theorem OrB_idempotent (a: St): <{ a | a }> <=> a.
Proof. intro m. simpl. apply orb_diag. Qed.

Theorem AndB_OrB_distrib_l (a b c: St): <{ (a | b) & c }> <=> <{ (a & c) | (b & c) }>.
Proof. intro m. simpl. apply andb_orb_distrib_l. Qed.

Theorem AndB_OrB_distrib_r (a b c: St): <{ a & (b | c) }> <=> <{ (a & b) | (a & c) }>.
Proof. intro m. simpl. apply andb_orb_distrib_r. Qed.

Theorem OrB_AndB_distrib_l (a b c: St): <{ (a & b) | c }> <=> <{ (a | c) & (b | c) }>.
Proof. intro m. simpl. apply orb_andb_distrib_l. Qed.

Theorem OrB_AndB_distrib_r (a b c: St): <{ a | (b & c) }> <=> <{ (a | b) & (a | c) }>.
Proof. intro m. simpl. apply orb_andb_distrib_r. Qed.

Theorem DNLB (a: St): <{ ~ ~ a }> <=> a.
Proof. intro m. simpl. apply negb_involutive. Qed.

Theorem TautologyBLaw (a b: St): TautologyB b -> <{ a & b }> <=> a.
Proof.
  unfold TautologyB, ConstB. intros H m. simpl.
  rewrite H. apply andb_true_r.
Qed.

Theorem TautologyLaw (a b: St):
  TautologyP b -> forall m, eval_prop m <{ a & b }> <-> eval_prop m a.
Proof.
  unfold TautologyP. intros H m. simpl. intuition.
Qed.

Theorem ContradictionBLaw (a b: St): ContradictionB b -> <{ a | b }> <=> a.
Proof.
  unfold ContradictionB, ConstB. intros H m. simpl.
  rewrite H. apply orb_false_r.
Qed.

Theorem ContradictionLaw (a b: St):
  ContradictionP b -> forall m, eval_prop m <{ a | b }> <-> eval_prop m a.
Proof.
  unfold ContradictionP. intros H m. simpl. split.
  - intros [Ha | Hb].
    + exact Ha.
    + contradict Hb. apply H.
  - intro Ha. left. exact Ha.
Qed.

Theorem ConditionalBLaw1 (a b: St): <{ a -> b }> <=> <{ ~a | b }>.
Proof. intro m. simpl. apply implb_orb. Qed.

Theorem ConditionalBLaw2 (a b: St): <{ a -> b }> <=> <{ ~(a & ~b) }>.
Proof.
  rewrite ConditionalBLaw1. rewrite DMLB2. rewrite DNLB. reflexivity.
Qed.

Theorem ContrapositiveBLaw (a b: St): <{ a -> b }> <=> <{ ~b -> ~a }>.
Proof.
  rewrite !ConditionalBLaw1. rewrite DNLB. apply OrB_comm.
Qed.

Theorem BiconditionalLaw (a b: St): <{ a <-> b }> <=> <{ (a -> b) & (b -> a) }>.
Proof.
  intro m. simpl. unfold Bool.eqb.
  destruct (eval m a) eqn:eqa, (eval m b) eqn:eqb; try reflexivity.
Qed.

(* Problem 4. Show that (P → R) ∧ (Q → R) ⇔ (P ∨ Q) → R, using logic laws. *)
Theorem ex4: <{ (P -> R) & (Q -> R) }> <=> <{ (P | Q) -> R }>.
Proof.
  rewrite !ConditionalBLaw1. rewrite DMLB1.
  rewrite <- OrB_AndB_distrib_l. reflexivity.
Qed.

(* Problem 5. Let A and B be any two sets.
Show that x ∉ A\B is equivalent to the statement x ∉ A or x ∈ B. *)
(* Remember definition from 1_Naive.v:
 Definition Diff (a b: NSet) := { x | x ∈ a /\ ~ x ∈ b }. *)
Theorem not_in_diff: <{ ~ ("x ∈ A" & ~ "x ∈ B") }> <=> <{ ~ "x ∈ A" | "x ∈ B" }>.
Proof. rewrite DMLB2. rewrite DNLB. reflexivity. Qed.

(** Exercises 1.2 *)

Theorem Ex1_2_1: <{ ~(P -> Q) }> <=> <{ P & ~Q }>.
Proof. intro m. simpl. destruct (m P), (m Q); reflexivity. Qed.

Theorem Ex1_2_1': <{ ~(P -> Q) }> <=> <{ P & ~Q }>.
Proof. rewrite ConditionalBLaw2. rewrite DNLB. reflexivity. Qed.

(* ex 1.2.2. *)
Check (BiconditionalLaw P Q). (* : <{ P <-> Q }> <=> <{ (P -> Q) & (Q -> P) }> *)

Theorem Ex1_2_3: P <=> <{ ~ P -> (Q & ~ Q) }>.
Proof.
  rewrite ConditionalBLaw1. rewrite DNLB.
  rewrite (ContradictionBLaw P). { reflexivity. }
  apply ContradictionAndB.
Qed.

Theorem Ex1_2_4: <{ (P | Q) & R }> </=> <{ P & R | P & Q }>.
Proof.
  unfold EqB. intro H.
  pose (H (P !-> true; Q !-> true; R !-> false; _ !-> false)) as C.
  simpl in C. unfold SMap_update in C. simpl in C. discriminate C.
Qed.

Theorem Ex1_2_5: <{ (P -> Q) & (P -> R) }> <=> <{ P -> (Q & R) }>.
Proof.
  rewrite !ConditionalBLaw1. rewrite <- OrB_AndB_distrib_r. reflexivity.
Qed.

Theorem Ex1_2_6: <{ (P -> R) | (Q -> R) }> <=> <{ P & Q -> R }>.
Proof.
  rewrite !ConditionalBLaw1. rewrite DMLB2. rewrite <- !OrB_assoc.
  rewrite (OrB_comm R). rewrite <- OrB_assoc. rewrite OrB_idempotent.
  reflexivity.
Qed.

Theorem Ex1_2_7: <{ P -> (Q -> R) }> <=> <{ (P & Q) -> R }>.
Proof.
  rewrite !ConditionalBLaw1. rewrite DMLB2. apply OrB_assoc.
Qed.

Theorem Ex1_2_8': <{ (P -> Q) -> R }> <=> <{ P -> (Q -> R) }>.
Proof.
  intro m. simpl. destruct (m P), (m Q), (m R); try reflexivity.
  (* we have counter examples here *)
Abort.

Theorem Ex1_2_8: <{ (P -> Q) -> R }> </=> <{ P -> (Q -> R) }>.
Proof.
  intros H. pose (H (P !-> F; Q !-> T; R !-> F; _ !-> F)) as C.
  simpl in C. unfold SMap_update in C. simpl in C.
  discriminate C.
Qed.
