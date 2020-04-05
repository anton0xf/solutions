Require Import Nat.
Require Import Vector.
Import VectorNotations.

Definition lock (n : nat) := Vector.t bool n.

Definition Transition (from to : lock) : Prop := OneChanged.
