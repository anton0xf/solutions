(** ListSet as a paramtric module *)
Require Import Arith.
Require Import ListSet.
Require List.

Module Type Key.
  Parameter A: Set.
  Parameter eq_dec: forall x y:A, {x = y} + {x <> y}.
End Key.

Module NatKey <: Key.
  Definition A := nat.
  Definition eq_dec := Nat.eq_dec.
End NatKey.

Module LSet(K: Key).
  Definition set := ListSet.set K.A.
  Definition empty := empty_set K.A.
  Definition add := set_add K.eq_dec.
  Definition single (x: K.A) := add x empty.
  Definition union := set_union K.eq_dec.
  Definition union3 (s1 s2 s3: set) := union s1 (union s2 s3).
  Definition In := @set_In K.A. 

  Declare Scope set_scope.
  Delimit Scope set_scope with set.
  Bind Scope set_scope with set.

  Infix "+:" := add (at level 60, right associativity): set_scope.
  (* Notation "x +: xs" := (add x xs) (at level 60, right associativity). *)
  Notation "{ }" := empty (format "{ }"): set_scope.
  Notation "{ x }" := (add x empty) (format "{ x }"): set_scope.
  Notation "{ x ; .. ; y }" := (add x .. (add y empty) ..)
                                 (format "{ x ; .. ; y }"): set_scope.
  Open Scope set_scope.

  Definition map {X: Type}: (X -> K.A) -> ListSet.set X -> set := set_map K.eq_dec.

  Fixpoint flat_map (f: K.A -> set) (s: set): set :=
    match s with
    | List.nil => empty
    | List.cons h t => union (f h) (flat_map f t)
    end.
End LSet.

Module NatSet := LSet NatKey.

Section NatSetExample.
  Import NatSet.
  Check empty : set. (* {} : set *)
  Check (add 1 empty) : set. (* {1} : set *)
  Check 4 +: {} : set. (* {4} : set *)
  Check {1;2;3} : set. (* {1;2;3} : set *)
  Check 1 +: 2 +: 3 +: empty : set. (* {1;2;3} : set *)
  Check map S {1;2;3}. (* map S {1;2;3} : set *)
  (* Example map_ex: map S {1;2;3} = {2;3;4}. *)
  (* Proof. simpl. reflexivity. Qed. *)

End NatSetExample.
