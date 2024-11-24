(* AST definition of simple Arith language *)
Inductive Term: Set :=
| TTrue
| TFalse
| TZero
| TSucc (t: Term)
| TPred (t: Term)
| TIsZero (t: Term)
| TIf (cond thenBr elseBr: Term).

Example TTrue_neq_TFalse: TTrue <> TFalse.
Proof. discriminate. Qed.
