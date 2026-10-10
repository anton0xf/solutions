Require Import Basics FunctionalExtensionality ProofIrrelevance Description.
From ACat Require Import Util Cat Functor.
From ACat Require Import TypeC Magma Semigroup Monoid.

Open Scope cat_scope.
Open Scope magma_scope.

Record group :=
  mk_group {
      group_monoid:> monoid;
      inv: group_monoid.(M) -> group_monoid.(M);
      inv_left (x: group_monoid.(M)): (inv x) * x = group_monoid.(mid);
      inv_right (x: group_monoid.(M)): x * (inv x) = group_monoid.(mid);
    }.

Arguments inv {g}.

Definition group_as_cat (g: group): cat := monoid_as_cat g.(group_monoid).

Record group_hom (dom cod: group) :=
  mk_group_hom {
      group_monoid_hom:> monoid_hom dom cod;
      respect_inv (x: dom.(M)): let f := group_monoid_hom.(map)
                                in f (inv x) = inv (f x);
    }.

Definition group_hom_id (g: group): group_hom g g.
  refine {| group_monoid_hom := monoid_hom_id g |}.
  intro x. unfold monoid_hom_id. simpl. reflexivity.
Defined.

Definition group_hom_comp {x y z: group}
  (f: group_hom y z) (g: group_hom x y): group_hom x z.
  refine {| group_monoid_hom := monoid_hom_comp f g |}.
  intros a. unfold monoid_hom_comp. simpl. unfold compose.
  rewrite !respect_inv. reflexivity.
Defined.

Theorem group_hom_ext {x y: group} (f g: group_hom x y):
  f.(map) = g.(map) -> f = g.
Proof.
  intro H. destruct f as [f fr], g as [g gr]. simpl in H.
  apply monoid_hom_ext in H as H0. subst g. f_equal.
  apply proof_irrelevance.
Qed.

Definition cat_group: cat.
  refine {|
      ob := group;
      hom := group_hom;
      id := group_hom_id;
      comp := @group_hom_comp;
    |}; intros; apply group_hom_ext; reflexivity.
Defined.

Definition forget: functor cat_group cat_monoid.
  unshelve eapply (mk_functor cat_group cat_monoid
                     group_monoid group_monoid_hom);
    try reflexivity.
Defined.
  
