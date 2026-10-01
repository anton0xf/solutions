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

Record pointed_fun (dom cod: pointed) :=
  mk_pointed_fun {
      pmap: dom.(carrier) -> cod.(carrier);
      pmap_point: pmap dom.(point) = cod.(point);
    }.

Arguments pmap {dom} {cod}.
Arguments pmap_point {dom} {cod}.

Definition pointed_fun_id {x: pointed}: pointed_fun x x :=
  {|
    pmap := Datatypes.id;
    pmap_point := eq_refl;
  |}.

Definition pointed_fun_comp {x y z: pointed}
  (f: pointed_fun y z) (g: pointed_fun x y): pointed_fun x z.
  refine {| 
      pmap := compose f.(pmap) g.(pmap);
    |}.
  unfold compose.
  replace (g.(pmap) x.(point)) with y.(point).
  - exact f.(pmap_point).
  - symmetry. exact g.(pmap_point).
Defined.  

Definition cat_of_pointed: cat.
  unshelve
    refine {|
        ob := pointed;
        hom x y := pointed_fun x y;
        id := @pointed_fun_id;
        comp := @pointed_fun_comp;
    |}.
  - (* id_left *) intros x y f.
    unfold pointed_fun_id, pointed_fun_comp. simpl.
    unfold compose, Datatypes.id.
    destruct f as [g gp]. simpl. f_equal.
    apply proof_irrelevance.
  - (* id_right *) intros x y f.
    unfold pointed_fun_id, pointed_fun_comp. simpl.
    unfold compose, Datatypes.id.
    destruct f as [g gp]. simpl. f_equal.
  - (* comp *) intros x y z t f g h.
    unfold pointed_fun_comp. simpl. f_equal.
    apply proof_irrelevance.
Qed.
