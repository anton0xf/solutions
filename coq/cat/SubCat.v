Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat.

Open Scope cat_scope.

Set Universe Polymorphism.

Record subcat (C: cat) :=
  {
    sub_ob: C.(ob) -> Prop;
    sub_hom {x y: C.(ob)}: x ~> y -> Prop;
    sub_dom {x y: C.(ob)} (f: x ~> y): sub_hom f -> sub_ob x;
    sub_cod {x y: C.(ob)} (f: x ~> y): sub_hom f -> sub_ob y;
    sub_id (x: C.(ob)): sub_hom (C.(@id) x);
    sub_comp {x y z: C.(ob)} (f: y ~> z) (g: x ~> y)
    : sub_hom f -> sub_hom g -> sub_hom (f ∘ g);
  }.

Arguments sub_ob {C s}.
Arguments sub_hom {C s x y}.
Arguments sub_dom {C s x y}.
Arguments sub_cod {C s x y}.
Arguments sub_id {C s}.
Arguments sub_comp {C s x y z f g}.

Definition subcat_as_cat (C: cat) (s: subcat C): cat.
  refine {|
      ob := { x: C.(ob) | s.(sub_ob) x };
      hom x y := { f: (proj1_sig x) ~> (proj1_sig y) | s.(sub_hom) f };
      id x := exist _ id (s.(sub_id) (proj1_sig x));
      comp x y z f g := exist _ (proj1_sig f ∘ proj1_sig g)
                          (s.(sub_comp) (proj2_sig f) (proj2_sig g));
    |}.
  - (* id_left *) intros a b [f Hf].
    apply subset_eq_compat. simpl. apply id_left.
  - (* id_right *) intros a b [f Hf].
    apply subset_eq_compat. simpl. apply id_right.
  - (* assoc *) intros a b c d [f Hf] [g Hg] [h Hh]. simpl.
    apply subset_eq_compat. apply assoc.
Qed.
