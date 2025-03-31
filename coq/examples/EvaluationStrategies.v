Require Import Arith.
Require Import Bool.

Compute false && (fact 10 =? 0).
Compute (fact 10 =? 0) && false.
Eval cbv in false && (fact 10 =? 0). (* long *)
Eval cbn in false && (fact 10 =? 0). 

Eval cbv in fact 10 =? 0. (* long *)
Eval cbn in fact 10 =? 0.
