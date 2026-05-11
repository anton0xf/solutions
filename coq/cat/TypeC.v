Require Import Basics FunctionalExtensionality List.
Require String BinInt.
From ACat Require Import Cat Functor.
  
Open Scope cat_scope.
Open Scope program_scope.

Definition type: cat.
  refine {|
      ob := Type;
      hom X Y := X -> Y;
      comp X Y Z f g := g ∘ f;
      id X x := x;
    |}.
  - (* id_left  *) reflexivity.
  - (* id_rigth *) reflexivity.
  - (* assoc *) reflexivity.
Defined.

Notation "a ~~~ b" := (@isomorphic type a b) (at level 70, no associativity).

Module ObjectIso.
  Import String BinInt.

  Record object :=
    mk_object {
        label: string;
        x: Z;
        y: Z;
      }.

  Example object_iso: object ~~~ (string * Z * Z)%type.
  Proof.
    unfold isomorphic.
    pose (fun obj => (obj.(label), obj.(x), obj.(y))) as f.
    exists f. unfold isomorphism.
    pose (fun tup => match tup with (lab, x, y) => mk_object lab x y end) as g.
    exists g. unfold inversion, inverse.
    split; apply functional_extensionality.
    - intro obj. simpl. destruct obj as [lab x y]. simpl. reflexivity.
    - intros [[lab x] y]. reflexivity.
  Qed.
End ObjectIso.

Record type_functor :=
  mk_type_functor {
      tmap: Type -> Type;
      fmap {A B: Type} (f: A -> B): tmap A -> tmap B;
      fmap_id {A: Type}: @fmap A A type.(id) = type.(id);
      fmap_comp {A B C: Type} (f: A -> B) (g: B -> C): fmap (g ∘ f) = fmap g ∘ fmap f;
    }.

Definition type_functor_to_functor (F: type_functor): functor type type.
  apply (mk_functor type type
           (* map_ob *) (F.(tmap))
           (* map_hom *) (fun A B (f: A -> B) => F.(fmap) f)
           (* preserve_id *) (fun _ => F.(fmap_id))).
  (* preserve_comp *) intros A B C f g. simpl. apply F.(fmap_comp).
Qed.

Definition option_functor: type_functor.
  refine {|
      tmap := option;
      fmap := option_map;
    |}.
  - (* id *) intro A. apply functional_extensionality.
    intro x. simpl. unfold option_map. destruct x; reflexivity.
  - (* comp *) intros A B C f g. apply functional_extensionality.
    intro x. destruct x; reflexivity.
Qed.

Definition list_functor: type_functor.
  refine {|
      tmap := list;
      fmap := map;
    |}.
  - (* id *) intro A. apply functional_extensionality.
    intro x. apply map_id.
  - (* comp *) intros A B C f g. apply functional_extensionality.
    intro x. unfold compose. rewrite <- map_map. reflexivity.
Qed.

(* Definition type_functor_compose: *)

(* Definition option_list_functor:  *)
