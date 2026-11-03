Require Import Basics FunctionalExtensionality ProofIrrelevance.

From ACat Require Import Cat Functor.
  
Open Scope cat_scope.

Set Universe Polymorphism.

Definition catc: cat.
  refine {|
      ob := cat;
      hom := functor;
      id := id_functor;
      comp := @functor_compose;
    |}; intros; apply functor_eq; exists eq_refl; reflexivity.
Defined.

Notation "a ~~~ b" := (@isomorphic catc a b)
                        (at level 70, no associativity): cat_scope.
