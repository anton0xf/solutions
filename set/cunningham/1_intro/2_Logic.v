(** 1.2 Logical Notation *)
Require Import Setoid.
From Stdlib Require Import Classical.
From Stdlib Require Import List.
Import ListNotations.
Open Scope bool_scope.
Require Import Nat.
From Stdlib Require Import NaryFunctions.

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
Definition ConstB (b: bool) (n: nat) (f: bool^^n --> bool): Prop :=
  forall x: bool^n, nuncurry bool bool n f x = b.

(** Definition 1.2.1. *)
Definition TautologyB := ConstB true.

Theorem LEMB: TautologyB 1 (fun p => p || negb p).
Proof.
  unfold TautologyB, ConstB. destruct x. simpl.
  destruct b; reflexivity.
Qed.
  
(** Definition 1.2.2. *)
Definition ContradictionB := ConstB false.

Example ContradictionB__ex: ContradictionB 1 (fun p => p && negb p).
Proof.
  unfold ContradictionB, ConstB. destruct x. simpl.
  destruct b; reflexivity.
Qed.
