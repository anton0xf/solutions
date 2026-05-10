Require Import Cat Basics.

Open Scope cat_scope.

Record functor :=
  mk_functor {
      src: cat;
      dst: cat;
      map_ob: src.(ob) -> dst.(ob);
      map_hom {a b: src.(ob)}: src.(hom) a b -> dst.(hom) (map_ob a) (map_ob b);
      preserve_id {a: src.(ob)}: map_hom (@id src a) = (@id dst (map_ob a));

      preserve_comp {a b c: src.(ob)} (f: src.(hom) a b) (g: src.(hom) b c):
      map_hom (g ∘ f) = map_hom g ∘ map_hom f;
    }.

(* endofunctor *)
Definition id_functor (C: cat): functor :=
  {|
    src := C;
    dst := C;
    map_ob x := x;
    map_hom _ _ f := f;
    preserve_id _ := eq_refl;
    preserve_comp _ _ _ _ _ := eq_refl;
  |}.

Definition const_functor (src dst: cat) (d: dst.(ob)): functor.
  refine {|
      src := src;
      dst := dst;
      map_ob _ := d;
      map_hom _ _ _ := @id dst d;
      preserve_id _ := eq_refl;
    |}.
  intros a b c f g. rewrite id_left. reflexivity.
Qed.

Definition cast {X Y : Type} (H : X = Y) (x : X) : Y :=
  match H with
  | eq_refl => x
  end.

Definition functor_compose (G F: functor) (H: F.(dst) = G.(src)): functor.
  refine {|
      src := F.(src);
      dst := G.(dst);
      (* map_ob := compose G.(map_ob) F.(map_ob); *)
    |}.
  Unshelve.
  3:{ intro x. pose (F.(map_ob) x) as y.
      apply G.(map_ob). rewrite <- H. exact y. }
  3:{ intros a b f. simpl. apply G.(map_hom).
      pose (F.(map_hom) f) as g.
      generalize dependent g.
      remember (F.(map_ob) a) as Fa eqn:def_Fa.
      remember (F.(map_ob) b) as Fb eqn:def_Fb.
      intro g. rewrite <- H. simpl. exact g. }
  - (* id *) simpl. intro a.
    set (Fa := F.(map_ob) a).
    pose (@preserve_id F a) as F_id.
    Check G.(preserve_id).

