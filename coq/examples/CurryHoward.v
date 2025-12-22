Require Import Arith.
Import Nat.

(* L expression
   * variable
   * M - L-expr -> [fun x => M] - abstraction
   * M, N - L-expr -> [M N] - application
 *)

Check (fun x => S x).

Compute (fun x => S x) 1.

(* b-reduction *)
Compute (fun x => S x) 1.
Eval lazy beta in (fun x => S x) 1.
Compute S 1.

(* https://en.wikipedia.org/wiki/Church_encoding *)

(* infinite loop | Y-combinator *)

(* Simply-typed
   * x: T - variable
   * M: B - L-expr -> [fun x: A => M]: (A -> B) - abstraction
   * M: A -> B, N: A - L-expr -> [M N]: B - application
*)

Check even. (* : nat -> bool *)
Check even 2. (* : bool *)

Check (fun x => (fun y: Set => even x)). (* [nat -> (Set -> bool) ] *)

Check (fun x => x).

Theorem idt (A: Prop): A -> A.
Proof. intro H. exact H. Qed.

Definition idt' (A: Prop): A -> A := (fun x => x).

Check (idt True).

Theorem trans (A B C: Prop): (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros HAB HBC HA.
  apply HBC. apply HAB. exact HA.
Qed.

Definition trans' (A B C: Prop): (A -> B) -> (B -> C) -> (A -> C) :=
  fun HAB HBC HA => HBC (HAB HA).

(* BHK-interpretation *)

