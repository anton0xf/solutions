Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor Structures.TypeC.
  
Open Scope cat_scope.

Record magma :=
  mk_magma {
      M:> Type;
      mu: M -> M -> M;
    }.

Arguments mu {m}.

Declare Scope magma_scope.
Delimit Scope magma_scope with magma.
Bind Scope magma_scope with magma.

Notation "x * y" := (mu x y): magma_scope.

Open Scope magma_scope.

Definition cast_mu {M N: Type} (H: M = N) (mu: M -> M -> M): N -> N -> N.
  subst M. exact mu.
Defined.

Theorem magma_eq (M N: Type) (mu: M -> M -> M) (nu: N -> N -> N)
  (HM: M = N)
  (Hmu: cast_mu HM mu = nu):
  mk_magma M mu = mk_magma N nu.
Proof. subst N nu. reflexivity. Qed.  

Record magma_hom (dom cod: magma) :=
  mk_magma_hom {
      map: dom -> cod;
      respect (x y: dom): map (x * y) = map x * map y;
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

Theorem magma_hom_ext {x y: magma} (f g: magma_hom x y):
  f.(map) = g.(map) -> f = g.
Proof.
  intros H. destruct f as [f fr], g as [g gr].
  simpl in H. subst g. f_equal. apply proof_irrelevance.
Qed.

Definition cat_magma: cat.
  refine {|
      ob := magma;
      hom x y := magma_hom x y;
      id := magma_hom_id;
      comp := @magma_hom_comp;
    |}.
  - (* id_left *) intros x y f. apply magma_hom_ext. reflexivity.
  - (* id_right *) intros x y f. apply magma_hom_ext. reflexivity.
  - (* assoc *) intros x y z t f g h.
    apply magma_hom_ext. reflexivity.
Defined.

Definition forget: functor cat_magma type.
  unshelve eapply (mk_functor cat_magma type (* map_ob *) M).
  - (* map_hom *) intros x y [f _]. exact f.
  - (* preserve_id *) intros x. simpl. reflexivity.
  - (* preserve_comp *) intros x y z g f. simpl. reflexivity.
Defined.
