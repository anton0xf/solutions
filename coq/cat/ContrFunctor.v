Require Import Cat.

Open Scope cat_scope.

Record contr_functor :=
  mk_contr_functor {
      src: cat;
      dst: cat;
      map_ob: src.(ob) -> dst.(ob);
      map_hom {a b: src.(ob)}: a ~> b -> (map_ob b) ~> (map_ob a);
      preserve_id {a: src.(ob)}: map_hom (@id src a) = (@id dst (map_ob a));

      preserve_comp {a b c: src.(ob)} (f: a ~> b) (g: b ~> c):
      map_hom (g ∘ f) = map_hom f ∘ map_hom g;
    }.


Definition op (C: cat): contr_functor.
  refine {|
      src := C;
      dst := {|
              ob := C.(ob);
              hom (a b: C.(ob)) := C.(hom) b a;
              comp (a b c: C.(ob)) (f: b ~> a) (g: c ~> b) := f ∘ g;
            |};
      map_ob (a: C.(ob)) := a;
      map_hom (a b: C.(ob)) (f: C.(hom) a b) := f;
      (* preserve_id (a: C.(ob)) := eq_refl; *)
      (* preserve_comp (a b c: C.(ob)) (f: a ~> b) (g: b ~> c) := eq_refl; *)
    |}.
  Unshelve.
  - (* preserve_id *) reflexivity.
  - (* preserve_comp *) reflexivity.
  - (* dst.(id_left) *) intros a b f. apply C.(id_right).
  - intros a b f. apply C.(id_left).
  - intros a b c d f g h. symmetry. apply C.(assoc).
Defined.  
  
Theorem terminal_op {C: cat} (x: C.(ob)):
  let C_op := op C in
  initial x <-> terminal (C_op.(map_ob) x).
Proof.
  intro C_op. simpl. unfold initial. split; intro H.
  - (* initial -> terminal *) intro y. apply H.
  - (* terminal -> initial *) intro y. apply H.
Qed.    
