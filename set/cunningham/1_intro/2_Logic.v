(** 1.2 Logical Notation *)
Require Import Setoid.
Require Import Morphisms.
From Stdlib Require Import Classical.
From Stdlib Require Import List. Import ListNotations.
Require Import Bool.
Require Import Nat.
From Stdlib Require Import Strings.String.

Open Scope bool_scope.

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

Definition SMap (X: Type) := string -> X.
Definition SMap_default {X: Type} (x: X): SMap X := fun _ => x.
Definition SMap_update {X: Type} (m: SMap X) (k: string) (x: X): SMap X :=
  fun s => if s =? k then x else m s.

Notation "'_' '!->' x" := (SMap_default x) (at level 100, right associativity).
Notation "k '!->' x ';' m" :=
  (SMap_update m k x) (at level 100, k constr, right associativity).

Definition PQ_vals: list (SMap bool) :=
  map (fun '(p, q) => (P !-> p; Q !-> q; _ !-> F)) (list_prod bvals bvals).

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

Definition ConstB (b: bool) (s: St): Prop := forall m, eval m s = b.

(** Definition 1.2.1. *)
Definition TautologyB := ConstB true.

Definition TautologyP (s: St) := forall m, eval_prop m s.

Theorem LEMB: TautologyB <{ P | ~P }>.
Proof. intros m. simpl. destruct (m P); reflexivity. Qed.

Example LEMP: TautologyP <{ P | ~P }>.
Proof. intros m. simpl. destruct (classic (m P)); auto. Qed.

(** Definition 1.2.2. *)
Definition ContradictionB := ConstB false.

Definition ContradictionP (s: St) := forall m, ~ eval_prop m s.

Example ContradictionB__ex: ContradictionB <{ P & ~P }>.
Proof. intros m. simpl. destruct (m P); reflexivity. Qed.

Example ContradictionP__ex: ContradictionP <{ P & ~P }>.
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
  unfold Proper, respectful, EqB.
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

(* De Morgan’s Laws *)
Theorem DMLB1 (p q: St): <{ ~(p | q) }> <=> <{ ~p & ~q }>.
Proof.
  unfold EqB. intro m. simpl.
  destruct (eval m p), (eval m q); reflexivity.
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

