Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor Structures.TypeC.
  
Open Scope cat_scope.

Record preorder :=
  mk_preorder {
      X: Type;
      le: X -> X -> Prop where "x <= y" := (le x y);
      le_refl x: x <= x;
      le_trans x y z: x <= y -> y <= z -> x <= z;
    }.

Arguments le {p}.
Arguments le_refl {p}.
Arguments le_trans {p} {x y z}.

Declare Scope order_scope.
Delimit Scope order_scope with order.
Bind Scope order_scope with preorder.
Notation "x <= y" := (le x y): order_scope.
Open Scope order_scope.

Definition preorder_as_cat (p: preorder): cat.
  refine {|
      ob := p.(X);
      hom x y := x <= y;
      id := le_refl;
      comp (x y z: p.(X)) (f: y <= z) (g: x <= y) := le_trans g f;
    |}; intros; apply proof_irrelevance.
Defined.

Record preorder_hom (dom cod: preorder) :=
  mk_preorder_hom {
    map: dom.(X) -> cod.(X);
    respect_le (x y: dom.(X)): x <= y -> map x <= map y;
  }.

Arguments map {dom cod}.
Arguments respect_le {dom cod}.

Definition preorder_hom_id (p: preorder): preorder_hom p p.
  refine {| map := Datatypes.id |}.
  intros x y H. unfold Datatypes.id. exact H.
Defined.

Definition preorder_hom_comp {a b c: preorder}
  (f: preorder_hom b c) (g: preorder_hom a b): preorder_hom a c.
  refine {| map := compose f.(map) g.(map) |}.
  intros x y H. unfold compose.
  apply f.(respect_le), g.(respect_le). exact H.
Defined.

Theorem preorder_hom_ext {a b: preorder} (f g: preorder_hom a b):
  f.(map) = g.(map) -> f = g.
Proof.
  intro H. destruct f as [f fr], g as [g gr]. simpl in H.
  subst g. f_equal. apply proof_irrelevance.
Qed.

Definition cat_preorder: cat.
  refine {|
      ob := preorder;
      hom := preorder_hom;
      id := preorder_hom_id;
      comp := @preorder_hom_comp;
    |}; intros; apply preorder_hom_ext; reflexivity.
Defined.
