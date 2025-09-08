(** 1.2 Logical Notation *)
Require Import Setoid.
From Stdlib Require Import Classical.
From Stdlib Require Import List.
Import ListNotations.

Definition bvals := [true; false].

(* Problem 1. Construct a truth table for the sentence ¬ P → (Q ∧ P) *)
Definition pr1 (p q: bool) := implb (negb p) (andb q p).

Compute map (fun '(p, q) => (p, q, pr1 p q)) (list_prod bvals bvals).
(* = [(true,  true,  true);
      (true,  false, true);
      (false, true,  false);
      (false, false, false)] *)
Example pr1_is_p (p q: bool): pr1 p q = p.
Proof. destruct p, q; reflexivity. Qed.
