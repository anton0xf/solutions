Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor.
  
Open Scope cat_scope.

Record magma :=
  mk_magma {
      M: Type;
      mu: M -> M -> M;
    }.

Arguments mu {m}.

Declare Scope magma_scope.
Delimit Scope magma_scope with magma.
Bind Scope magma_scope with magma.

Notation "x * y" := (mu x y): magma_scope.

Open Scope magma_scope.

Record magma_hom (dom cod: magma) :=
  mk_magma_hom {
      map: dom.(M) -> cod.(M);
      respect (x y: dom.(M)): map (x * y) = map x * map y;
    }.

Arguments map {dom} {cod}.
Arguments respect {dom} {cod}.

Definition magma_hom_id (m: magma): magma_hom m m.
  refine {| map := Datatypes.id |}.
  intros x y. unfold Datatypes.id. reflexivity.
Defined.

Definition magma_hom_comp {x y z: magma}
  (f: magma_hom y z) (g: magma_hom x y): magma_hom x z.
  refine {| map := compose f.(map) g.(map) |}.
  intros a b. unfold compose.
  rewrite g.(respect), f.(respect). reflexivity.
Defined.

Definition cat_magma: cat.
  refine {|
      ob := magma;
      hom x y := magma_hom x y;
      id := magma_hom_id;
      comp := @magma_hom_comp;
    |}.
  - (* id_left *) intros x y f.
    unfold magma_hom_id, magma_hom_comp, compose, Datatypes.id. simpl.
    destruct f as [fmap frespect]. simpl. f_equal.
    apply proof_irrelevance.
  - (* id_right *) intros x y f.
    unfold magma_hom_id, magma_hom_comp, compose, Datatypes.id. simpl.
    destruct f as [fmap frespect]. simpl. f_equal.
    apply proof_irrelevance.
  - (* assoc *) intros x y z t f g h.
    unfold magma_hom_comp, compose. simpl. f_equal.
    apply proof_irrelevance.
Defined.
