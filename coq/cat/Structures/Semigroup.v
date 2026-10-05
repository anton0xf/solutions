Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor Structures.TypeC Structures.Magma.
  
Open Scope cat_scope.
Open Scope magma_scope.

Record semigroup :=
  mk_semigroup {
      semigroup_magma:> magma;
      mu_assoc (x y z: semigroup_magma.(M)): x * (y * z) = (x * y) * z;
    }.

Record semigroup_hom (dom cod: semigroup) :=
  mk_semigroup_hom {
      semigroup_magma_hom:> magma_hom dom cod;
      respect_assoc (x y z: dom): x * (y * z) = (x * y) * z ->
                                  let f := semigroup_magma_hom.(map) in
                                  f x * (f y * f z) = (f x * f y) * f z;
    }.

Arguments respect_assoc {dom} {cod}.

Definition semigroup_hom_id (x: semigroup): semigroup_hom x x.
  refine {| semigroup_magma_hom := magma_hom_id x |}.
  intros a b c H. simpl. unfold Datatypes.id. exact H.
Defined.

Definition semigroup_hom_comp {a b c: semigroup}
  (f: semigroup_hom b c) (g: semigroup_hom a b): semigroup_hom a c.
  refine {| semigroup_magma_hom := @magma_hom_comp a b c f g |}.
  intros x y z H. simpl.
  apply f.(respect_assoc), g.(respect_assoc), H.
Defined.

Theorem semigroup_hom_ext {x y: semigroup} (f g: semigroup_hom x y):
  f.(map) = g.(map) -> f = g.
Proof.
  intros H. destruct f as [f fr], g as [g gr].
  simpl in H. apply magma_hom_ext in H as Hm.
  subst g. f_equal. apply proof_irrelevance.
Qed.

Definition cat_semigroup: cat.
  refine {|
      ob := semigroup;
      hom := semigroup_hom;
      id := semigroup_hom_id;
      comp := @semigroup_hom_comp;
    |}.
  - (* id_left *) intros a b f. apply semigroup_hom_ext. reflexivity.
  - (* id_right *) intros a b f. apply semigroup_hom_ext. reflexivity.
  - (* assoc *) intros. apply semigroup_hom_ext. reflexivity.
Defined.

Definition forget: functor cat_semigroup cat_magma.
  unshelve eapply (mk_functor cat_semigroup cat_magma semigroup_magma).
  - intros a b f. exact f.
  - reflexivity.
  - reflexivity.
Qed.
