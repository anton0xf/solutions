Parameter Term : Set.
Parameter TrueTerm : Term.
Parameter FalseTerm : Term.
Axiom Term_neq: TrueTerm <> FalseTerm.
Axiom Term_min: forall t: Term, t = TrueTerm \/ t = FalseTerm.

Theorem not_true_is_false (t: Term): t <> TrueTerm -> t = FalseTerm.
Proof.
  intro neq. destruct (Term_min t) as [eq|eq].
  - contradiction.
  - exact eq.
Qed.
