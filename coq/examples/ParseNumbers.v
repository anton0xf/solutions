Require Import Arith Ascii String Decimal DecimalString.
Import NilEmpty Nat.

Check uint.
Compute uint_of_string "123".
Check rev.
Compute option_map of_uint (uint_of_string "123").
