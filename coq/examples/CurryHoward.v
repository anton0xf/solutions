Require Import Arith.
Import Nat.

(*
   expr ::= '(' expr ')' | expr1 {('*' | '/') expr}
   expr1 := number {('+' | '-') expr1}
   number ::= [sign] digit+
   sign ::= '+' | '-'
   digit ::= '0'..'9'

   expr:
   0
   +4+3*-5
 *)

(* https://en.wikipedia.org/wiki/Lambda_calculus
   L expression [𝑒 ::= 𝑥 ∣ 𝜆⁢𝑥.𝑒 ∣ ⁢𝑒𝑒]
   * variable
   * M - L-expr -> [fun x => M] - abstraction
   * M, N - L-expr -> [M N] - application
 *)

Check (fun x => S x).

Compute (fun x => S x) 1.

(* b-reduction *)
Compute (fun x => S x) 1. (* S 1 *) 
Eval lazy beta in (fun x => S x) 1.
Compute S 1.

(* https://en.wikipedia.org/wiki/Church_encoding *)

(* infinite loop | Y-combinator *)
(*

loop := (λx.xx)(λx.xx) => (x x)[x := (λx.xx)] => (λx.xx)
id := (λ y.x)
const := (λ x.(λ y.x))
(const id) loop

 *)

(*
  P x := x is a pig
  Pigs := {x | P x}

 A ∪ B := { x | x ∈ A ∨ x ∈ B }
 A ∩ B := { x | x ∈ A ∧ x ∈ B }

 https://en.wikipedia.org/wiki/Russell%27s_paradox

 R := { x | x ∉ x }
 x ∈ R ⇔ x ∉ x
 R ∈ R ⇔ R ∉ R
 A ⇔ ¬A

 S₀ - individuals (prohibited: x ∈ y: S₀)
 S₁ - sets of individuals (x: S₀) ∈ (y: S₁)
 (x: Sₙ) ∈ (y: S_{n+1})
 
*)

(* Simply-typed
   * x: T - variable
   * M: B - L-expr -> [fun x: A => M]: (A -> B) - abstraction
   * M: A -> B, N: A - L-expr -> [M N]: B - application
*)

(* loop := (λx.xx)(λx.xx) *)
Fail Check (fun x => x x).
(* (λx:T.(x:T != T->V) (x:T)): T->V *)

Check even. (* : nat -> bool *)
Check even 2. (* : bool *)

Check (fun x => (fun y: Set => even x)). (* [nat -> (Set -> bool) ] *)

Check (fun x => x).

(* https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence *)
(* M: T <=> T - tautology in Iimpl
   Iimpl - implicative fragment of Intuitionistic logic
 *)

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

