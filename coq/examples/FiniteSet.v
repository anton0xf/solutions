Require Import Coq.MSets.MSetInterface.
(* Require Import Coq.MSets.MSetAVL. *)
Require Import Coq.MSets.MSetList.
Require Import Coq.Structures.OrdersEx.
(* Module NatSet := MSetAVL.Make(Nat_as_DT). *)
Module NatSet := MSetList.Make(Nat_as_DT).

Theorem add_creates_non_empty :
  forall (x: Nat_as_OT.t),
  ~ NatSet.Empty (NatSet.add x NatSet.empty).
Proof.
  intros x C. unfold NatSet.Empty in C. apply (C x).
  apply NatSet.add_spec. left. reflexivity.
Qed.

Theorem add_creates_non_empty' :
  forall (x: Nat_as_OT.t),
  ~ NatSet.Empty (NatSet.add x NatSet.empty).
Proof.
  intros x H. simpl in H.

Theorem union_identity : forall s: NatSet.t,
    NatSet.Equal (NatSet.union s NatSet.empty) s.
Proof.
  intros.
  unfold NatSet.Equal.
  intros x.
  rewrite NatSet.union_spec. intuition.
  exfalso. 
  pose NatSet.empty_spec as E. unfold NatSet.Empty in E.
  apply (E x), H0.
Qed.

Require Import Coq.Arith.PeanoNat. (* For basics of nat and <= *)

Lemma example_cardinal (n: nat) (s: NatSet.t):
  NatSet.cardinal s <= NatSet.cardinal (NatSet.add n s).
Proof.
  destruct (NatSet.mem n s) eqn:Hmem.
  - (* Case: n is already in the set *)
    apply NatSet.mem_spec in Hmem. 
    (* If n is in s, adding it again doesn't change the cardinality *)
    apply Nat.eq_le_incl. apply f_equal.
    admit.
  - (* Case: n is not in the set *)
    (* Adding n increases the cardinality by 1 *)
Admitted.

(*
NatSet.add_spec:
  forall (s : NatSet.t) (x y : NatSet.elt),
  NatSet.In y (NatSet.add x s) <-> y = x \/ NatSet.In y s

NatSet.mem_spec:
  forall (s : NatSet.t) (x : NatSet.elt), NatSet.mem x s = true <-> NatSet.In x s

NatSet.cardinal_spec: forall s : NatSet.t, NatSet.cardinal s = length (NatSet.elements s)

NatSet.elements_spec2: forall s : NatSet.t, Sorted lt (NatSet.elements s)
NatSet.elements_spec2w: forall s : NatSet.t, NoDupA eq (NatSet.elements s)
NatSet.elements_spec1:
  forall (s : NatSet.t) (x : NatSet.elt), InA eq x (NatSet.elements s) <-> NatSet.In x s

*)

Open Scope nat_scope.

Module NatSet := MSetList.Make(Nat_as_OT).

Definition s1 : NatSet.t := NatSet.empty.  (* Create an empty set *)
Definition s2 : NatSet.t := NatSet.add 5 s1.  (* Add an element *)
Definition s3 : NatSet.t := NatSet.add 3 s2.  (* Add another element *)

Check NatSet.mem 3 s3.  (* Check membership *)
Compute NatSet.mem 3 s3.

Lemma example_property (n: nat) (s: NatSet.t): NatSet.mem n (NatSet.add n s) = true.
Proof.
  apply NatSet.mem_spec.
  apply NatSet.add_spec.
  left. reflexivity.
Qed.

Compute NatSet.cardinal s3.
