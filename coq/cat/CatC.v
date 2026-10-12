Require Import Basics FunctionalExtensionality ProofIrrelevance.

From ACat Require Import Cat Functor.
  
Open Scope cat_scope.

Definition cat_cat: cat.
  refine {|
      ob := cat;
      hom := functor;
      id := id_functor;
      comp := @functor_compose;
    |}; intros; apply functor_eq; exists eq_refl; reflexivity.
Defined.
