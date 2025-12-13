Inductive nat := O: nat | S: nat -> nat.

Fixpoint plus (a b: nat): nat :=
  match a with
  | O => O
  | S a => S (plus a b)
  end.
