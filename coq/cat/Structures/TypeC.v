Require Import Basics FunctionalExtensionality ProofIrrelevance.
Require Import List Fin FinFun Program.Equality.
Require String BinInt.
From ACat Require Import Cat Functor.
  
Open Scope cat_scope.
Open Scope program_scope.

Definition type_as_cat (T: Type): cat.
  unshelve refine {|
      ob := T;
      hom a b := a = b;
    |}.
  - (* comp *) intros a b c Hbc Hab. apply eq_trans with b; assumption.
  - (* id *) reflexivity.
  - (* id_left *) intros x y Hxy. simpl. reflexivity.
  - (* id_right *) intros x y Hxy. simpl. apply proof_irrelevance.
  - (* assoc *) intros x y z t Hxy Hyz Hzt. simpl.
    apply proof_irrelevance.
Defined.

(* TODO: prove it's descrete skeletal category *)

Definition type: cat.
  refine {|
      ob := Type;
      hom X Y := X -> Y;
      comp X Y Z g f := g ∘ f;
      id X x := x;
    |}.
  - (* id_left  *) reflexivity.
  - (* id_rigth *) reflexivity.
  - (* assoc *) reflexivity.
Defined.

Notation "a ~~~ b" := (@isomorphic type a b)
                        (at level 70, no associativity): cat_scope.

Theorem iso_means_bijection (X Y: Type): X ~~~ Y <-> exists f: X -> Y, Bijective f.
Proof.
  unfold isomorphic, isomorphism, inversion, inverse, Bijective. split.
  - (* -> *) intros [f [g [H1 H2]]]. unfold hom in *. simpl in *.
    exists f, g. split; intro x.
    + exact (f_equal (fun h => h x) H1).
    + exact (f_equal (fun h => h x) H2).
  - (* <- *) intros [f [g [H1 H2]]].
    exists f, g. split; apply functional_extensionality; intro x;
      simpl; unfold compose.
    + apply H1.
    + apply H2.
Qed.

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

  Example object_iso': object ~~~ (string * Z * Z)%type.
  Proof.
    apply iso_means_bijection.
    pose (fun obj => (obj.(label), obj.(x), obj.(y))) as f.
    exists f. unfold Bijective.
    pose (fun tup => match tup with (lab, x, y) => mk_object lab x y end) as g.
    exists g. split.
    - intros [lab x y]. reflexivity.
    - intros [[lab x] y]. reflexivity.
  Qed.

End ObjectIso.

Record type_functor :=
  mk_type_functor {
      tmap: Type -> Type;
      fmap {A B: Type} (f: A -> B): tmap A -> tmap B;
      fmap_id {A: Type}: @fmap A A type.(id) = type.(id);
      fmap_comp {A B C: Type} (g: B -> C) (f: A -> B): fmap (g ∘ f) = fmap g ∘ fmap f;
    }.

Definition type_functor_as_functor (F: type_functor): functor type type.
  apply (mk_functor type type
           (* map_ob *) (F.(tmap))
           (* map_hom *) (fun A B (f: A -> B) => F.(fmap) f)
           (* preserve_id *) (fun _ => F.(fmap_id))).
  (* preserve_comp *) intros A B C f g. simpl. apply F.(fmap_comp).
Defined.

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

Definition type_functor_compose (G F: type_functor): type_functor.
  refine {|
      tmap := G.(tmap) ∘ F.(tmap);
      fmap _ _ := G.(fmap) ∘ F.(fmap);
    |}.
  - (* id *) intro A. unfold compose.
    rewrite F.(fmap_id). apply G.(fmap_id).
  - (* comp *) intros A B C g f.
    assert (forall (X Y: Type) (h: X -> Y),
               (G.(fmap) ∘ F.(fmap)) h = G.(fmap) (F.(fmap) h))
      as E by reflexivity.
    rewrite !E. rewrite F.(fmap_comp). rewrite G.(fmap_comp). reflexivity.
Defined.

(* \circledbullet *)
Notation "F ⦿ G" := (type_functor_compose G F)
                      (at level 40, left associativity): cat_scope.

Theorem type_functor_compose_correct (G F: type_functor):
  type_functor_as_functor (G ⦿ F) = type_functor_as_functor G ⊚ type_functor_as_functor F.
Proof.
  unfold type_functor_as_functor. simpl. 
  unfold functor_compose. simpl.
  f_equal. apply functional_extensionality_dep.
  intro x. f_equal. apply proof_irrelevance.
Qed.

Definition option_list_functor: type_functor := option_functor ⦿ list_functor.

Definition fin := Fin.t.

Theorem unit_iso_one: unit ~~~ fin 1.
Proof.
  apply iso_means_bijection. exists (fun _ => F1).
  unfold Bijective. exists (fun _ => tt).
  split; intro x.
  - destruct x. reflexivity.
  - dependent destruction x.
    + reflexivity.
    + dependent destruction x.
Qed.

Theorem unit_fun_iso (X: Type): (unit -> X) ~~~ X.
Proof.
  apply iso_means_bijection.
  exists (fun f => f tt). unfold Bijective.
  exists (fun x _ => x). split.
  - intro f. apply functional_extensionality.
    intro x. destruct x. reflexivity.
  - reflexivity.
Qed.
