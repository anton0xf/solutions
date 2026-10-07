Require Import Basics FunctionalExtensionality ProofIrrelevance Description.
From ACat Require Import Util Cat Functor.
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

Theorem monoid_eq (a b: monoid)
  (Hs: a.(monoid_semigroup) = b.(monoid_semigroup))
  (Hid: cast (semigroup_carrier_eq Hs) a.(mid) = b.(mid)):
  a = b.
Proof.
  destruct a, b. simpl in Hs. subst monoid_semigroup1.
  simpl in Hid. subst mid1. unfold semigroup_carrier_eq.
  f_equal; apply proof_irrelevance.
Qed.

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

Definition is_mid {m: semigroup} (e: m.(M)): Prop :=
  forall x, e * x = x /\ x * e = x.

Record monoid_alt :=
  mk_monoid_alt {
      monoid_alt_semigroup:> semigroup;
      mid_exists: exists e: monoid_alt_semigroup.(M), is_mid e;
    }.

Theorem monoid_alt_eq {m n: monoid_alt}
  (H: m.(monoid_alt_semigroup) = n.(monoid_alt_semigroup)):
  m = n.
Proof.
  destruct m as [m mmid], n as [n nmid]. simpl in H.
  subst n. f_equal. apply proof_irrelevance.
Qed.

Definition monoid_to_alt (m: monoid): monoid_alt.
  refine {| monoid_alt_semigroup := m.(monoid_semigroup) |}.
  exists m.(mid). intro x. split.
  - apply m.(mid_left).
  - apply m.(mid_right).
Defined.

Theorem mid_unique (m: monoid_alt) (e1 e2: m.(M)):
  is_mid e1 -> is_mid e2 -> e1 = e2.
Proof.
  unfold is_mid. intros H1 H2.
  destruct (H1 e2) as [_ H12r].
  destruct (H2 e1) as [H21l _].
  rewrite <- H21l. exact H12r.
Qed.

Definition alt_mid (m : monoid_alt) : { e : m.(M) | is_mid e }.
  apply constructive_definite_description.
  destruct m.(mid_exists) as [e He].
  exists e. split.
  - exact He.
  - intros e' He'. apply mid_unique; assumption.
Defined.

Definition monoid_from_alt (m: monoid_alt): monoid.
  pose (alt_mid m) as H.
  destruct H as [e H]. unfold is_mid in H.
  refine {|
      monoid_semigroup := m.(monoid_alt_semigroup);
      mid := e;
    |}.
  - intro x. apply H.
  - intro x. apply H.
Defined.

Theorem monoid_alt_iso: monoid ~~~ monoid_alt.
Proof.
  apply iso_means_bijection.
  exists monoid_to_alt. exists monoid_from_alt.
  split; intro m.
  - unfold monoid_to_alt, monoid_from_alt. simpl.
    match goal with
    | |- (let (x, i) := ?p in _) = _ =>
        destruct p as [e H]
    end.
    simpl in e. unshelve eapply monoid_eq. { reflexivity. }
    simpl. apply (@mid_unique (monoid_to_alt m) e mid H).
    destruct m. simpl in e. unfold is_mid. intros x. split; auto.
  - unfold monoid_to_alt. destruct m as [m mmid]. unfold monoid_from_alt.
    match goal with
    | |- context [alt_mid ?x] =>
        destruct (alt_mid x) as [e He]
    end.
    simpl. f_equal. apply proof_irrelevance.
Qed.
