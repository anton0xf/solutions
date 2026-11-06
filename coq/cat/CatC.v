Require Import Basics FunctionalExtensionality ProofIrrelevance JMeq.
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

Theorem embedding_iff_mono (b c: catc.(ob)) (f: b ~> c):
  embedding f <-> monomorphism f.
Proof.
  split.
  - intros [H1 H2] a g1 g2 H. simpl in *.
    assert (Hg: forall x: a.(ob), map_ob g1 x = map_ob g2 x).
    { unfold ob_injective, injective in H1.
      intro x. apply H1.
      replace (map_ob f (map_ob g1 x)) with (map_ob (f ⊚ g1) x) by reflexivity.
      rewrite H. reflexivity. }
    apply functor_ext.
    + apply Hg.
    + unfold faithful, injective in H2.
      intros a1 a2 h.
      assert (H2': forall (i: map_ob g1 a1 ~> map_ob g1 a2)
                     (j: map_ob g2 a1 ~> map_ob g2 a2),
                 JMeq (map_hom f i) (map_hom f j) -> JMeq i j).
      { intros i j Hij. rewrite <- !Hg in j.
        apply JMeq_eq in Hij.
        apply H2 in Hij. subst j. reflexivity. }
      apply H2'.
