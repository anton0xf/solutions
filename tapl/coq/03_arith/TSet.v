Require Import TAPL_03_Arith.Arith.
Require Import ListSet.

Theorem Term_eq_dec: forall t1 t2: Term, {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.
Definition tset := set Term.
Definition tset_empty := empty_set Term.
Definition tset_add := set_add Term_eq_dec.
Definition tset_single (t: Term) := tset_add t tset_empty.
Definition tset_union := set_union Term_eq_dec.
Definition tset_union3 (s1 s2 s3: tset) := tset_union s1 (tset_union s2 s3).
