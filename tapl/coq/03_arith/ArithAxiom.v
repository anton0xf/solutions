(* axiomatic definition of grammar *)
Require Import Arith.
Require Import List.
Import ListNotations.

Parameter Term : Set.
Parameter TTrue : Term.
Parameter TFalse : Term.
Parameter TZero: Term.
Parameter TSucc: Term -> Term.
Parameter TPred: Term -> Term.
Parameter TIsZero: Term -> Term.
Parameter TIf: Term -> Term -> Term -> Term.

Axiom Term_uniq: forall t1 t2 t3: Term,
    NoDup [TTrue; TFalse; TZero; TSucc t1; TPred t1; TIsZero t1; TIf t1 t2 t3].

Axiom Term_min: forall t: Term,
    t = TTrue \/ t = TFalse \/ t = TZero
    \/ (exists t1: Term, t = TSucc t1 \/ t = TPred t1 \/ t = TIsZero t1)
    \/ (exists t1 t2 t3: Term, t = TIf t1 t2 t3).

Example true_neq_false: TTrue <> TFalse.
Proof.
  pose (U := Term_uniq TZero TZero TZero).
  apply NoDup_cons_iff in U as [true_not_in _].
  simpl in true_not_in. auto.
Qed.
