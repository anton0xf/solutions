(* proof of Functor Laws for Functor List
see ./functor_list.hs *)

Require Import List.
Require Import Basics.
Import ListNotations.

Fixpoint fmap {a b : Type} (f : a -> b) (xs : list a) : list b
  := match xs with
     | [] => []
     | x :: xs => (f x) :: (fmap f xs)
     end.

Theorem functorLaw1 {a : Type} (xs : list a) : fmap id xs = xs.
Proof.
  induction xs as [| x xs' IH].
  - (* xs = [] *) reflexivity.
  - (* xs = x :: xs' *)
    simpl. rewrite IH. reflexivity.
Qed.

Theorem functorLaw2 {a b c : Type} (f : b -> c) (g : a -> b) (xs : list a)
  : fmap (compose f g) xs = compose (fmap f) (fmap g) xs.
Proof.
  induction xs as [| x xs' IH].
  - (* xs = [] *) reflexivity.
  - (* xs = x :: xs' *) simpl. rewrite IH. reflexivity.
Qed.
