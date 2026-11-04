Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor CatC Simple.

Open Scope cat_scope.

Set Universe Polymorphism.

Record subcat (C: cat) :=
  {
    sub_ob: C.(ob) -> Prop;
    sub_hom {x y: C.(ob)}: x ~> y -> Prop;
    sub_id (x: C.(ob)): sub_ob x -> sub_hom (C.(@id) x);
    sub_comp {x y z: C.(ob)} (f: y ~> z) (g: x ~> y)
    : sub_hom f -> sub_hom g -> sub_hom (f ∘ g);
  }.

Arguments sub_ob {C s}.
Arguments sub_hom {C s x y}.
Arguments sub_id {C s}.
Arguments sub_comp {C s x y z f g}.

Definition subcat_as_cat {C: cat} (s: subcat C): cat.
  refine {|
      ob := { x: C.(ob) | s.(sub_ob) x };
      hom x y := { f: (proj1_sig x) ~> (proj1_sig y) | s.(sub_hom) f };
      id x := exist _ id (s.(sub_id) (proj1_sig x) (proj2_sig x));
      comp x y z f g := exist _ (proj1_sig f ∘ proj1_sig g)
                          (s.(sub_comp) (proj2_sig f) (proj2_sig g));
    |}.
  - (* id_left *) intros a b [f Hf].
    apply subset_eq_compat. simpl. apply id_left.
  - (* id_right *) intros a b [f Hf].
    apply subset_eq_compat. simpl. apply id_right.
  - (* assoc *) intros a b c d [f Hf] [g Hg] [h Hh]. simpl.
    apply subset_eq_compat. apply assoc.
Defined.

Definition inclusion {C: cat} (s: subcat C): functor (subcat_as_cat s) C.
  unfold subcat_as_cat. simpl.
  refine {|
      map_ob (x: (subcat_as_cat s).(ob)) := proj1_sig x;
      map_hom (x y: (subcat_as_cat s).(ob)) (f: x ~> y) := proj1_sig f;
    |}; reflexivity.
Defined.

Theorem inclusion_is_embedding {C: cat} (s: subcat C): embedding (inclusion s).
Proof.
  split.
  - unfold ob_injective, injective. intros [x Hx] [y Hy] H.
    simpl in H. subst y. f_equal. apply proof_irrelevance.
  - unfold faithful, injective. intros x y [f Hf] [g Hg] H.
    simpl in *. subst g. f_equal. apply proof_irrelevance.
Qed.

Module Empty.

  Definition E: cat.
    apply (@subcat_as_cat singleton).
    refine {|
        sub_ob _ := False;
        sub_hom _ _ _ := False;
      |}.
    - (* sub_id *) intros x H. exact H.
    - (* sub_comp *) intros x y z f g Hf Hg. exact Hf.
  Defined.

  Definition F: catc.(hom) E empty.
    refine {|
        map_ob (x: E.(ob)) := match proj2_sig x with end;
        map_hom (x y: E.(ob)) (f: E.(hom) x y) :=
          match proj2_sig f with end;
      |}; intros [a []].
  Defined.

  Definition G: catc.(hom) empty E.
    refine {|
        map_ob (x: empty.(ob)) := match x with end;
        map_hom (x y: empty.(ob)) (f: empty.(hom) x y) :=
          match x with end;
      |}; intros [].
  Defined.

  Theorem E_is_empty: E ~~~ empty.
  Proof.
    exists F, G. unfold inversion, inverse. simpl.
    split; apply functor_ext; try intros [_ []]; intros [].
  Qed.

End Empty.

Module Singleton.

  Definition S: cat.
    apply (@subcat_as_cat singleton).
    refine {|
        sub_ob _ := True;
        sub_hom _ _ _ := True;
      |}.
    - (* sub_id *) intros. exact I.
    - (* sub_comp *) intros. exact I.
  Defined.

  Definition F: catc.(hom) S singleton.
    refine {|
        map_ob (x: S.(ob)) := tt: singleton.(ob);
        map_hom _ _ _ := tt;
      |}; reflexivity.
  Defined.

  Definition G: catc.(hom) singleton S.
    refine {|
        map_ob (x: singleton.(ob)) := exist _ x I : S.(ob);
        map_hom (x y: singleton.(ob)) (f: x ~> y) := exist _ f I;
      |}; reflexivity.
  Defined.

  Theorem FG: F ⊚ G = id_functor S.
  Proof.
    apply functor_ext.
    - intros [[] Hx]. simpl in *. f_equal. apply proof_irrelevance.
    - intros [[] Hx] [[] Hy] [[] Hf]. simpl in *.
      assert (Hf = I) by (apply proof_irrelevance). subst Hf.
      reflexivity.
  Qed.

  Theorem GF: G ⊚ F = id_functor singleton.
    apply functor_ext.
    - intros []. simpl. reflexivity.
    - intros [] [] []. simpl. reflexivity.
  Qed.

  Theorem S_is_singleton: S ~~~ singleton.
  Proof.
    exists F, G. unfold inversion, inverse. simpl.
    split; [apply FG | apply GF].
  Qed.

End Singleton.
