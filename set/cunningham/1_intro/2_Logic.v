(** 1.2 Logical Notation *)
Require Import Setoid.
From Stdlib Require Import Classical.
From Stdlib Require Import List.
Import ListNotations.
Open Scope bool_scope.
Require Import Nat.
From Stdlib Require Import NaryFunctions.
Import SigTNotations.

Definition bvals := [true; false].

(* Problem 1. Construct a truth table for the sentence ¬ P → (Q ∧ P) *)
Definition pr1 (p q: bool) := implb (negb p) (q && p).

Compute map (fun '(p, q) => (p, q, pr1 p q)) (list_prod bvals bvals).
(* = [(true,  true,  true);
      (true,  false, true);
      (false, true,  false);
      (false, false, false)] *)
Example pr1_is_p (p q: bool): pr1 p q = p.
Proof. destruct p, q; reflexivity. Qed.

(* use NaryFunctions *)
Check (bool^^3 --> bool).

(* sentence *)
Definition Snt := { n: nat & bool^^n --> bool }. (* sigT *)
About sigT.
About existT.
Check (existT (fun n => bool^^n --> bool)).
Check (existT (fun n => bool^^n --> bool) 2 andb) : Snt.
Check (existT _ 2 andb) : Snt.

Definition mkSnt (n: nat) (f: bool^^n --> bool): Snt := existT _ n f.
Check mkSnt 2 andb.

Notation "s .n" := (projT1 s) (at level 1, left associativity, format "s .n").
Compute (mkSnt 2 andb).n.

Notation "s .f" := (projT2 s) (at level 1, left associativity, format "s .f").
Compute (mkSnt 2 andb).f.

(* uncurry sentence function *)
Definition Snt_unc (s: Snt): bool^s.n -> bool := nuncurry bool bool s.n s.f.

Definition ConstB (b: bool) (s: Snt): Prop := forall x: bool^s.n, Snt_unc s x = b.

(** Definition 1.2.1. *)
Definition TautologyB := ConstB true.

Theorem LEMB: TautologyB (mkSnt 1 (fun p => p || negb p)).
Proof.
  unfold TautologyB, ConstB. destruct x. simpl.
  destruct b; reflexivity.
Qed.

(** Definition 1.2.2. *)
Definition ContradictionB := ConstB false.

Example ContradictionB__ex: ContradictionB (mkSnt 1 (fun p => p && negb p)).
Proof.
  unfold ContradictionB, ConstB. destruct x. simpl.
  destruct b; reflexivity.
Qed.

(** LogicalEquivalence *)

(** Definition 1.2.3.
    [P(X)] and [Q(X)] are logically equivalent (P <=> Q) iff [forall X: bool^n, P X = Q X] *)
Definition EqB (n: nat) (f g: bool^^n --> bool) := forall x: bool^n, nuncurry _ _ n f x = nuncurry _ _ n g x.

(* useless but interesting try to implement ideas from https://www.cis.upenn.edu/~plclub/blog/2020-05-15-Rewriting-in-Coq/ *)
Section Useless_EqB_props.

Instance EqB_refl (n: nat): Reflexive (EqB n).
Proof. unfold Reflexive, EqB. reflexivity. Qed.

Instance EqB_sym (n: nat): Symmetric (EqB n).
Proof. unfold Symmetric, EqB. auto. Qed.

Instance EqB_trans (n: nat): Transitive (EqB n).
Proof.
  unfold Transitive, EqB.
  intros f g h H1 H2 x. rewrite H1, H2. reflexivity.
Qed.

Instance EqB_equiv (n: nat): Equivalence (EqB n).
Proof.
  split. 
  - apply EqB_refl.
  - apply EqB_sym.
  - apply EqB_trans.
Qed.

Require Import Morphisms.
Instance EqB_negb_proper (n: nat): Proper (EqB n ==> EqB n) (nfun_to_nfun _ _ _ negb n).
Proof.
  unfold Proper, respectful, EqB.
  induction n as [| n IH].
  { simpl. intros p q H _. rewrite H.
    - reflexivity.
    - exact tt. }
  intros p q eq [b x]. simpl. apply (IH (p b) (q b)). clear IH x.
  simpl in eq. intro x. apply (eq (b, x)).
Qed.

End Useless_EqB_props.

(* De Morgan’s Laws *)
Theorem DMLB1 (p q: bool): negb (p || q) = negb p && negb q.
Proof. destruct p, q; reflexivity. Qed.

Theorem DMLB1': EqB 2 (fun p q => negb (p || q)) (fun p q => negb p && negb q).
Proof.
  unfold EqB. intros [p [q z]]. simpl. clear z.
  destruct p, q; reflexivity.
Qed.

Theorem DML1 (P Q: Prop): ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
  split; intro H.
  - split; intro C; apply H.
    + left. exact C.
    + right. exact C.
  - destruct H as [HnP HnQ]. intros [C | C]; auto.
Qed.

Theorem DMLB2 (p q: bool): negb (p && q) = negb p || negb q.
Proof. destruct p, q; reflexivity. Qed.

Theorem DML2 (P Q: Prop): ~(P /\ Q) <-> ~P \/ ~Q.
Proof.
  split; intro H.
  - destruct (classic P) as [HP | HnP].
    + right. auto.
    + left. exact HnP.
  - intros [HP HQ]. destruct H; contradiction.
Qed.
