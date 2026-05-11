Require Import Cat Basics.

Open Scope cat_scope.

Record functor (src dst: cat) :=
  mk_functor {
      map_ob: src.(ob) -> dst.(ob);
      map_hom {a b: src.(ob)}: src.(hom) a b -> dst.(hom) (map_ob a) (map_ob b);
      preserve_id {a: src.(ob)}: map_hom (@id src a) = (@id dst (map_ob a));

      preserve_comp {a b c: src.(ob)} (f: src.(hom) a b) (g: src.(hom) b c):
      map_hom (g ∘ f) = map_hom g ∘ map_hom f;
    }.

Arguments map_ob {src dst f0}.
Arguments map_hom {src dst f0 a b}.
Arguments preserve_id {src dst f0 a}.
Arguments preserve_comp {src dst f0 a b c}.

Definition endofunctor (C: cat) := functor C C.

Definition id_functor (C: cat): endofunctor C :=
  {|
    map_ob x := x;
    map_hom _ _ f := f;
    preserve_id _ := eq_refl;
    preserve_comp _ _ _ _ _ := eq_refl;
  |}.

Definition const_functor (src dst: cat) (d: dst.(ob)): functor src dst.
  refine {|
      map_ob _ := d;
      map_hom _ _ _ := @id dst d;
      preserve_id _ := eq_refl;
    |}.
  intros a b c f g. rewrite id_left. reflexivity.
Qed.

Definition functor_compose (A B C: cat) (G: functor B C) (F: functor A B)
  : functor A C.
  refine {|
      map_ob x := G.(map_ob) (F.(map_ob) x);
      map_hom _ _ f := G.(map_hom) (F.(map_hom) f);
    |}.
  - intro a. rewrite !preserve_id. reflexivity.
  - intros a b c f g. rewrite !preserve_comp. reflexivity.
Qed.

(* \circledcirc *)
Notation "F ⊚ G" := (functor_compose G F) (at level 40, left associativity): cat_scope.
