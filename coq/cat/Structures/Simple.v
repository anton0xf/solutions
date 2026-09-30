Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor.
  
Open Scope cat_scope.

(** empty *)
Definition empty :=
  mk_cat Empty_set (fun _ _ => Empty_set)
    (fun a _ _ _ _ => match a with end)
    (fun a => match a with end)
    (fun a _ _ => match a with end)
    (fun a _ _ => match a with end)
    (fun _ _ _ _ _ _ _ => eq_refl _).

Definition empty': cat.
  refine {|
      ob := Empty_set;
      hom _ _ := Empty_set;
      comp a _ _ _ _ := match a with end;
    |}; intro a; destruct a.
Defined.

Example empty_ob_id (a b: empty.(ob)): a = b.
Proof. destruct a. Qed.

Example empty_hom_id (a: empty.(ob)) (f: a ~> a): f = id.
Proof. destruct a. Qed.

Example empty_hom_comp_comm (a: empty.(ob)) (f g: a ~> a): f ∘ g = g ∘ f.
Proof. destruct a. Qed.

(** singleton *)
Definition singleton: cat.
  refine {|
      ob := unit;
      hom a b := unit;
      comp _ _ _ _ _ := tt;
      id _ := tt;
    |}.
  - (* id_left *) intros. destruct f. reflexivity.
  - (* id_right *) intros. destruct f. reflexivity.
  - (* assoc *) reflexivity.
Defined.

Example singleton_ob_id (a b: singleton.(ob)): a = b.
Proof. destruct a, b. reflexivity. Qed.

Example singleton_hom_id (a: singleton.(ob)) (f: a ~> a): f = id.
Proof. destruct f, id. reflexivity. Qed.

(** https://ncatlab.org/nlab/show/walking+morphism *)
Inductive two_ob := two0 | two1.

Inductive two_hom: two_ob -> two_ob -> Type :=
| two_id0: two_hom two0 two0
| two_id1: two_hom two1 two1
| two_mor: two_hom two0 two1.

Definition two_comp (a b c: two_ob)
  (g: two_hom b c) (f: two_hom a b): two_hom a c
  := match f, g with
     | two_id0, _ => g
     | two_id1, _ => g
     | two_mor, _ => match c with two0 => two_id0 | two1 => two_mor end
     end.

Definition two: cat.
 refine {|
     ob := two_ob;
     hom := two_hom;
     id a := match a with two0 => two_id0 | two1 => two_id1 end;
     comp := two_comp;
   |}.
 - (* id_left *) intros a b f. destruct f; reflexivity.
 - (* id_right *) intros a b f. destruct f; reflexivity.
 - (* assoc *) intros a b c d f g h.
   destruct f eqn:def_f; try reflexivity.
   inversion g. subst c. inversion h. subst d. reflexivity.
Defined.

Example two_not_iso (a b: two.(ob)): a ~~ b -> a = b.
Proof.
  unfold isomorphic, isomorphism, inversion, inverse.
  intros [f [g [H0 H1]]]. destruct a, b; try reflexivity.
  - inversion g.
  - inversion f.
Qed.
