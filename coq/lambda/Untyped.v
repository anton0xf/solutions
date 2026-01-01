(* https://en.wikipedia.org/wiki/Lambda_calculus *)
Require Import Arith String List ListSet.
Import Nat ListNotations Ascii.

(** Lambda expression *)
(* 𝑒 ::= 𝑥 ∣ 𝜆⁢𝑥.𝑒 ∣⁢ 𝑒𝑒 *)
Inductive LExpr :=
| LVar (name: string) 
| LApp (M N: LExpr)
| L (var: string) (body: LExpr).

(** short syntax *)
Open Scope string_scope.

(* see https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html#lab403 for details *)
Coercion LVar : string >-> LExpr.

Declare Custom Entry lam.

Notation "<{ x }>" := x (x custom lam).
Notation "( x )" := x (in custom lam, x at level 99).
Notation "x" := x (in custom lam at level 0, x constr at level 0).
Notation "x => y" := (L x y) (in custom lam at level 95, right associativity).
Notation "x y" := (LApp x y) (in custom lam at level 80, left associativity).

Definition x: string := "x".
Definition y: string := "y".
Definition z: string := "z".
Definition f: string := "f".
Definition g: string := "g".

Check <{ (x => x x) y }>.

Unset Printing Notations.
Check <{ (x => x x) y }>.
Set Printing Notations.

(** ListSet of strings helpers *)
Definition strs := set string.
Definition no_strs := empty_set string.
Definition add_str := set_add string_dec.
Definition one_str (s: string) := add_str s no_strs.
Definition strs_of (xs: list string): strs := nodup string_dec xs.
Definition strs_mem := set_mem string_dec.
Definition strs_In := set_In string.
Definition remove_str := set_remove string_dec.
Definition union_strs := set_union string_dec.

(** Free variables of Lambda expression *)
Fixpoint free_vars (M: LExpr): strs :=
  match M with
  | LVar name => one_str name
  | LApp M N => union_strs (free_vars M) (free_vars N)
  | L var body => remove_str var (free_vars body)
  end.

Example free_vars_ex: free_vars <{ (x => z x) y }> = strs_of [z; y].
Proof. reflexivity. Qed.

(** option helpers *)
(* fmap / <$>
   https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Prelude.html#v:fmap
   https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Prelude.html#v:-60--36--62- *)
Definition opt_fmap {A B: Type} (f: A -> B) (x: option A): option B :=
  match x with
  | Some x => Some (f x)
  | None => None
  end.
Notation "f <$> x" := (opt_fmap f x) (at level 55, left associativity).

(* ap / <*>
   https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Control-Monad.html#v:ap
   https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Prelude.html#v:-60--42--62- *)
Definition opt_ap {A B: Type} (f: option (A -> B)) (x: option A): option B :=
  match f, x with
  | Some f, Some x => Some (f x)
  | _, _ => None
  end.
Notation "f <*> x" := (opt_ap f x) (at level 55, left associativity).

Check pair <$> (Some 1) <*> (Some false) : option (nat * bool).
Compute pair <$> (Some 1) <*> (Some false). (* = Some (1, false) *)


(** substitution *)
(* The notation 𝑀⁡[𝑥:=𝑁] denotes capture-avoiding substitution:
substituting N for every free occurrence of x in M,
while avoiding variable capture. *)

Fixpoint subst (x: string) (M N: LExpr): option LExpr :=
  match M with
  | LVar name => Some (if name =? x then N else M)
  | LApp A B => LApp <$> subst x A N <*> subst x B N
  | L var body => if var =? x then Some M else
                   if strs_mem var (free_vars N) then None
                   else L var <$> subst x body N
  end.

Example subst_var_ex0: subst x y z = Some (LVar y).
Proof. reflexivity. Qed.

Example subst_var_ex1: subst x x z = Some (LVar z).
Proof. reflexivity. Qed.

Example subst_L_ex0: subst x <{ x => f y }> z = Some <{ x => f y }>.
Proof. reflexivity. Qed.

Example subst_L_ex1: subst x <{ y => f y }> <{ g y }> = None.
Proof. reflexivity. Qed.

Example subst_L_ex2: subst x <{ y => f x y }> z = Some <{ y => f z y }>.
Proof. reflexivity. Qed.

Example subst_ex: subst x <{ (y => f x y) (g x) }> z = Some <{ (y => f z y) (g z) }>.
Proof. reflexivity. Qed.



