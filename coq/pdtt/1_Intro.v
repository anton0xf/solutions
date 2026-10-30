Require Import Arith.
Import Nat.

Inductive Vec (A: Set): nat -> Set :=
| vnil: Vec A 0
| vcons (n: nat): A -> Vec A n -> Vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} {n}.

Notation "[ ]" := vnil.
Infix "::" := vcons (at level 60, right associativity).

Definition head {A: Set} {n: nat} (xs: Vec A (S n)): A :=
  match xs with
  | x :: _ => x
  end.
  
Definition tail {A: Set} {n: nat} (xs: Vec A (S n)): Vec A n :=
  match xs with
  | _ :: xs => xs
  end.

Fixpoint append {A: Set} {n m: nat} (xs: Vec A n) (ys: Vec A m): Vec A (n + m) :=
  match xs with
  | [] => ys
  | x :: xs => x :: append xs ys
  end.

Definition three := append (1 :: []) (2 :: 3 :: []).
Compute three.
Compute head three.
Compute tail three.

Fixpoint filter_len {A: Set} {n: nat} (f: A -> bool) (xs: Vec A n): nat :=
  match xs with
  | [] => 0 
  | x :: xs => let rest := filter_len f xs in
             if f x then S rest else rest
  end.

Fixpoint filter {A: Set} {n: nat} (f: A -> bool) (xs: Vec A n)
  : Vec A (filter_len f xs) :=
  match xs return Vec A (filter_len f xs) with
  | [] => []
  | x :: xs =>
      let rest_len := filter_len f xs in
      let rest := filter f xs in
      match f x as b return Vec A (if b then S rest_len else rest_len)
      with
      | true => x :: rest
      | false => rest
      end
  end.

Compute filter odd three.

Fixpoint filter_packed {A: Set} {n: nat} (f: A -> bool) (xs: Vec A n)
  : { k: nat & Vec A k } :=
  match xs with
  | [] => existT _ 0 []
  | x :: xs =>
      let '(existT _ k rest) := filter_packed f xs in
      if f x
      then existT _ (S k) (x :: rest)
      else existT _ k rest
  end.

Compute filter_packed odd three.
(* = existT (fun k : nat => Vec nat k) 2 (1 :: 3 :: [ ]) *)
(* : {k : nat & Vec nat k} *)

Theorem filter_len_to_empty {A: Set} {n: nat} (xs: Vec A n):
  filter_len (fun _ => false) xs = 0.
Proof.
  induction xs as [|n x xs IH]. { reflexivity. }
  simpl. exact IH.
Qed.

Theorem filter_len_max {A: Set} {n: nat} (f: A -> bool) (xs: Vec A n):
  filter_len f xs <= n.
Proof.
  induction xs as [|n x xs IH]. { apply le_n. }
  simpl. destruct (f x) eqn:H.
  - apply le_n_S. exact IH.
  - apply le_S. exact IH.
Qed.
