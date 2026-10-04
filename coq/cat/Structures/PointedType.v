Require Import Basics FunctionalExtensionality ProofIrrelevance.
From ACat Require Import Cat Functor Structures.TypeC.
  
Open Scope cat_scope.

Record pointed :=
  mk_pointed {
    carrier: Type;
    point: carrier;
  }.

Definition pointed_as_cat (p: pointed): cat := type_as_cat p.(carrier).
(* TODO: why is it a good definition? However it ignores point *)

Record pointed_hom (dom cod: pointed) :=
  mk_pointed_hom {
      map: dom.(carrier) -> cod.(carrier);
      map_point: map dom.(point) = cod.(point);
    }.

Arguments map {dom} {cod}.
Arguments map_point {dom} {cod}.

Definition pointed_hom_id {x: pointed}: pointed_hom x x :=
  {|
    map := Datatypes.id;
    map_point := eq_refl;
  |}.

Definition pointed_hom_comp {x y z: pointed}
  (f: pointed_hom y z) (g: pointed_hom x y): pointed_hom x z.
  refine {| 
      map := compose f.(map) g.(map);
    |}.
  unfold compose.
  replace (g.(map) x.(point)) with y.(point).
  - exact f.(map_point).
  - symmetry. exact g.(map_point).
Defined.

Definition cat_of_pointed: cat.
  unshelve
    refine {|
        ob := pointed;
        hom x y := pointed_hom x y;
        id := @pointed_hom_id;
        comp := @pointed_hom_comp;
    |}.
  - (* id_left *) intros x y f.
    unfold pointed_hom_id, pointed_hom_comp. simpl.
    unfold compose, Datatypes.id.
    destruct f as [g gp]. simpl. f_equal.
    apply proof_irrelevance.
  - (* id_right *) intros x y f.
    unfold pointed_hom_id, pointed_hom_comp. simpl.
    unfold compose, Datatypes.id.
    destruct f as [g gp]. simpl. f_equal.
  - (* comp *) intros x y z t f g h.
    unfold pointed_hom_comp. simpl. f_equal.
    apply proof_irrelevance.
Defined.

Definition forget: functor cat_of_pointed type.
  unshelve eapply (mk_functor cat_of_pointed type carrier).
  - (* map_hom *) intros x y [f _]. exact f.
  - (* preserve_id *) reflexivity.
  - (* preserve_comp *) reflexivity.
Defined.
