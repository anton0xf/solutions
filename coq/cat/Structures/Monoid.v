Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor.
From ACat Require Import TypeC Magma Semigroup.

Open Scope cat_scope.
Open Scope magma_scope.

Record monoid :=
  mk_monoid {
      monoid_semigroup:> semigroup;
      mid: monoid_semigroup.(M);
      mid_left x: mid * x = x;
      mid_right x: x * mid = x;
    }.

Arguments mid {_}.
Arguments mid_left {_}.
Arguments mid_right {_}.

Definition monoid_as_cat (m: monoid): cat.
Proof.
  refine {|
      ob := unit;
      hom _ _ := m.(M);
      comp _ _ _ x y := x * y;
      id _ := mid;
      id_left _ _ x := mid_left x;
      id_right _ _ x := mid_right x;
    |}.
  intros. apply mu_assoc.
Defined.

Definition singleton: cat.
Proof.
  apply monoid_as_cat.
  unshelve
    refine {|
        monoid_semigroup :=
          {|
            semigroup_magma :=
              {|
                M := unit;
                mu _ _ := tt;
              |};
          |};
        mid := tt;
      |}; intro x; destruct x; reflexivity.
Defined.

Record monoid_hom (dom cod: monoid) :=
  {
    monoid_magma_hom:> magma_hom dom cod;
    respect_mid: monoid_magma_hom.(map) dom.(mid) = cod.(mid);
  }.

Arguments respect_mid {dom} {cod}.

Definition monoid_hom_id (m: monoid): monoid_hom m m.
  refine {|
      monoid_magma_hom := magma_hom_id m;
    |}.
  reflexivity.
Defined.

Definition monoid_hom_comp {x y z: monoid}
  (f: monoid_hom y z) (g: monoid_hom x y): monoid_hom x z.
  refine {|
      monoid_magma_hom := magma_hom_comp f g;
    |}.
  simpl. unfold compose.
  rewrite g.(respect_mid), f.(respect_mid).
  reflexivity.
Defined.

Theorem monoid_hom_ext {x y: monoid} (f g: monoid_hom x y):
  f.(map) = g.(map) -> f = g.
Proof.
  destruct f as [f fr], g as [g gr]. simpl. intro H.
  apply magma_hom_ext in H as H0. subst g.
  f_equal. apply proof_irrelevance.
Qed.

Definition cat_monoid: cat.
  refine {|
      ob := monoid;
      hom := monoid_hom;
      id := monoid_hom_id;
      comp := @monoid_hom_comp;
    |}; intros; apply monoid_hom_ext; reflexivity.
Defined.

Definition forget: functor cat_monoid cat_semigroup.
  unshelve eapply (mk_functor cat_monoid cat_semigroup monoid_semigroup).
  - intros a b f. exact f.
  - reflexivity.
  - reflexivity.
Defined.
