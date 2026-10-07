Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor Structures.TypeC Structures.Magma.
  
Open Scope cat_scope.
Open Scope magma_scope.

Record semigroup :=
  mk_semigroup {
      semigroup_magma:> magma;
      mu_assoc (x y z: semigroup_magma.(M)): x * (y * z) = (x * y) * z;
    }.

Theorem semigoup_eq (a b: semigroup):
  a.(semigroup_magma) = b.(semigroup_magma) -> a = b.
Proof.
  intro H. destruct a as [a a_assoc], b as [b b_assoc].
  simpl in H. subst b. f_equal. apply proof_irrelevance.
Qed.

Definition semigroup_carrier_eq {a b: semigroup}: a = b -> a.(M) = b.(M).
  intros H. destruct H. reflexivity.
Defined.

Definition cat_semigroup: cat.
  refine {|
      ob := semigroup;
      hom := magma_hom;
      id := magma_hom_id;
      comp := @magma_hom_comp;
    |}.
  - (* id_left *) intros a b f. apply magma_hom_ext. reflexivity.
  - (* id_right *) intros a b f. apply magma_hom_ext. reflexivity.
  - (* assoc *) intros. apply magma_hom_ext. reflexivity.
Defined.

Definition forget: functor cat_semigroup cat_magma.
  unshelve eapply (mk_functor cat_semigroup cat_magma semigroup_magma).
  - intros a b f. exact f.
  - reflexivity.
  - reflexivity.
Defined.
