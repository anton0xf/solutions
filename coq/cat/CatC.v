Require Import Basics FunctionalExtensionality ProofIrrelevance JMeq.
From ACat Require Import Cat Functor Simple.
  
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
    + intros a1 a2 h. apply (faithful_JMeq f H2); try apply Hg.
      change (JMeq (map_hom (f ⊚ g1) h) (map_hom (f ⊚ g2) h)).
      rewrite H. reflexivity.
  - unfold monomorphism. intro HM. split.
    + intros x y H.
      apply (const_functor_eq (tt: singleton.(ob))).
      remember (const_functor singleton b x) as g1 eqn:H1.
      remember (const_functor singleton b y) as g2 eqn:H2.
      apply (HM singleton g1 g2).
      subst g1 g2. rewrite !const_functor_comp.
      rewrite <- H. reflexivity.
    + intros x y i j H. apply pick_hom_eq. apply HM.
      rewrite !pick_hom_comp. rewrite H. reflexivity.
Qed.
