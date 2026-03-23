Parameter T : Type.
Parameter g h a : T.

Definition f := (g, h).
Compute (f, a).
(* = (g, h, a) *)
(* : T * T * T *)

Compute (g, (h, a)).
(* = (g, (h, a)) *)
(* : T * (T * T) *)


