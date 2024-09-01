Require Import TAPL_03_Arith.Arith.
Require Import TAPL_03_Arith.TSet.
Require Import Arith.Arith.
Require Import List.
Require Import ListSet.
Import ListNotations.
Import Nat.

Fixpoint consts (t: Term): tset :=
  match t with
| TTrue => tset_single TTrue
| TFalse => tset_single TFalse
| TZero => tset_single TZero
| TSucc t => consts t
| TPred t => consts t
| TIsZero t => consts t
| TIf t1 t2 t3 => tset_union3 (consts t1) (consts t2) (consts t3)
end.
