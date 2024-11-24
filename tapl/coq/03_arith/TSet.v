Require Import TAPL_03_Arith.Term.
Require Import TAPL_03_Arith.SetUtil.
Require Import MSets MSetWeakList.

Theorem Term_eq_dec: forall t1 t2: Term, {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Module DecidableTerm <: UsualDecidableType.
  Definition t := Term.
  Definition eq := @eq t.
  Definition eq_equiv : Equivalence eq := eq_equivalence.
  Definition eq_dec := Term_eq_dec.
End DecidableTerm.

Module TSet := Make DecidableTerm.
Module TSetFacts := Facts TSet.
Module TSetNotations := SetNotations DecidableTerm TSet.
Module TSet1 := Set1 DecidableTerm TSet.
Module TSet2 := Set2 DecidableTerm DecidableTerm TSet TSet.

Section TSetExample.
  Import TSet.
  Import TSetNotations.

  Compute singleton TTrue.
  Check add TFalse (singleton TTrue).
  Check {TTrue;TZero}.
  Check TFalse +: {TTrue;TZero}.
  Check union {TFalse} {TTrue;TZero}.

  Import TSet2.
  Check map TSucc {TZero; TSucc TZero}.
End TSetExample.

(* Definition tset := set Term. *)
(* Definition tset_empty := empty_set Term. *)
(* Definition tset_add := set_add Term_eq_dec. *)
(* Definition tset_single (t: Term) := tset_add t tset_empty. *)
(* Definition tset_union := set_union Term_eq_dec. *)
(* Definition tset_union3 (s1 s2 s3: tset) := tset_union s1 (tset_union s2 s3). *)
(* Definition tset_In := set_In (A := Term). *)

(* Fixpoint tset_from_list (ts: list Term) := *)
(*   match ts with *)
(*   | nil => tset_empty *)
(*   | t :: ts' => tset_add t (tset_from_list ts') *)
(*   end. *)

(* Definition tset_map {A: Type}: (A -> Term) -> set A -> tset := set_map Term_eq_dec. *)

(* Fixpoint tset_flat_map (f: Term -> tset) (ts: tset): tset := *)
(*   match ts with *)
(*   | [] => tset_empty *)
(*   | t :: ts' => tset_union (f t) (tset_flat_map f ts') *)
(*   end. *)
