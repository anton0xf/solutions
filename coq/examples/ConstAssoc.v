Parameter X: Type.
Definition const (x y: X) := y.

Notation "x >> y" := (const x y) (at level 50, left associativity).

Theorem const_assoc (x y z: X): (x >> y) >> z = x >> (y >> z).
Proof. reflexivity. Qed.
  
