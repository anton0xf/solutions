Require Import Arith String List.
Import Nat Ascii ListNotations.

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
Compute three. (* = 1 :: 2 :: 3 :: [] : Vec nat (1 + 2) *)

Definition type_of {A : Type} (_ : A) : Type := A.

Compute (type_of three). (* = Vec nat 3 : Type *)
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

(** nary *)

Fixpoint nary (A: Set) (n: nat): Set :=
  match n with
  | 0 => A
  | S n => A -> nary A n
  end.

Fixpoint apply {A: Set} {n: nat} (f: nary A n) (xs: Vec A n): A :=
  match xs in Vec _ k return nary A k -> A with
  | [] => fun f => f
  | x :: xs => fun f => apply (f x) xs
  end f.

Compute apply (S: nary nat 1) (1 :: []).
Compute apply (add: nary nat 2) (1 :: 2 :: []).
Compute apply (n := 2) add (1 :: 2 :: []).

Definition apply' {A : Set} {n : nat}
  (xs : Vec A n) (f : nary A n) : A :=
  apply (n := n) f xs.

Compute apply' (1 :: 2 :: []) add.

Section DependentMatch.
  
  Definition T (b: bool) : Set := if b then nat else bool.

  Fail Definition f (b: bool) (x: T b): nat :=
    match b with
    | true => x (* The term "x" has type "T b" while it is expected to have type "nat". *)
    | false => if x then 1 else 0
    end.
  
  Definition f (b: bool) (x: T b): nat :=
    (match b return T b -> nat with
     | true => fun x => x
     | false => fun x => if x then 1 else 0
     end) x.
  
  Definition f' (b: bool) (x: T b): nat.
    destruct b.
    - simpl in x. exact x.
    - simpl in x. exact (if x then 1 else 0).
  Defined.

  Definition f'' (b: bool) (x: T b): nat :=
    (if b return (T b -> nat)
     then fun x: T true => x
     else fun x: T false => if x then 1 else 0
    ) x.

End DependentMatch.

(** printf *)
Open Scope list_scope.
Open Scope string_scope.

Inductive Token :=
| char: ascii -> Token
| strTok.

Open Scope char_scope.

Fixpoint lex (s: string): list Token :=
  match s with
  | ""%string => []
  | String "%" (String "%" s) => char "%" :: lex s
  | String "%" (String "s" s) => strTok :: lex s
  | String c s => char c :: lex s
  end.

Fixpoint args (ts: list Token) :=
  match ts with
  | [] => string
  | char _ :: ts => args ts
  | strTok :: ts => string -> args ts
  end.

Definition printfType (s: string) := args (lex s).

Definition sprintf (s: string): printfType s :=
  let fix iter (ts: list Token) (acc: string): args ts :=
    match ts with
    | [] => acc
    | char c :: ts => iter ts (acc ++ (String c ""%string))
    | strTok :: ts => fun s => iter ts (acc ++ s) 
    end
  in iter (lex s) ""%string.

Close Scope char_scope.
Compute printfType "%%a: %s, b: %s".
Compute sprintf "%%a: %s, b: %s" "aa" "bb".

Compute sprintf "a:%s".
Compute type_of (sprintf "a:%s").

Compute sprintf "a:%s, %s".
Compute type_of (sprintf "a:%s, %s").
