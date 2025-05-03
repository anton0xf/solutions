Require Import Arith.
Require Import Bool.

Compute false && (fact 10 =? 0).
Compute (fact 10 =? 0) && false.
Fail Eval cbv in false && (fact 10 =? 0). (* err *)
Eval cbn in (fact 10 =? 0).
Eval cbn in false && (fact 10 =? 0). 

Eval cbv in fact 10 =? 0. (* long *)
Eval cbn in fact 10 =? 0.
