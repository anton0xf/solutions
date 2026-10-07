Definition cast {A B: Type} (H: A = B) (a: A): B.
  subst B. exact a.
Defined.
