Require Import Basics ProofIrrelevance.
From ACat Require Import Cat.

Open Scope cat_scope.

Record functor (src dst: cat) :=
  mk_functor {
      map_ob: src.(ob) -> dst.(ob);
      map_hom {a b: src.(ob)}: src.(hom) a b -> dst.(hom) (map_ob a) (map_ob b);
      preserve_id {a: src.(ob)}: map_hom (@id src a) = (@id dst (map_ob a));

      preserve_comp {a b c: src.(ob)} (g: src.(hom) b c) (f: src.(hom) a b):
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
Defined.

Definition functor_compose {A B C: cat} (G: functor B C) (F: functor A B)
  : functor A C.
  refine {|
      map_ob x := G.(map_ob) (F.(map_ob) x);
      map_hom _ _ f := G.(map_hom) (F.(map_hom) f);
    |}.
  - intro a. rewrite !preserve_id. reflexivity.
  - intros a b c f g. rewrite !preserve_comp. reflexivity.
Defined.

(* \circledcirc *)
Notation "F ⊚ G" := (functor_compose G F) (at level 40, left associativity): cat_scope.

(* Check eq_ind. *)
(*[ forall [A: Type] (x: A) (P: A -> Prop), P x -> forall y: A, x = y -> P y ]*)

(* Check eq_rec. *)
(*[ forall [A: Type] (x: A) (P: A -> Set),  P x -> forall y: A, x = y -> P y ]*)

(* Check eq_rect. *)
(*[ forall [A: Type] (x: A) (P: A -> Type), P x -> forall y: A, x = y -> P y ]*)

Definition cast_hom_type (A B : cat) (m : A.(ob) -> B.(ob)) : Type :=
  forall a b : A.(ob), A.(hom) a b -> B.(hom) (m a) (m b).

Check (fun (A B: cat) (F: functor A B) => @map_hom A B F).
(* fun (A B : cat) (F : functor A B) => @map_hom A B F *)
(*      : forall (A B : cat) (F : functor A B) (a b : ob A), a ~> b -> map_ob a ~> map_ob b *)

Definition cast_map_hom_type {A B: cat} (F G: functor A B) (H: F.(map_ob) = G.(map_ob))
  : forall a b: A.(ob), a ~> b -> G.(map_ob) a ~> G.(map_ob) b := 
  eq_rect F.(map_ob) (cast_hom_type A B) (@map_hom A B F) G.(map_ob) H.

Check (forall (A B: cat) (F G: functor A B),
        exists H_ob : @map_ob A B F = @map_ob A B G,
          cast_map_hom_type F G H_ob = (@map_hom A B G)).

Theorem functor_eq {A B: cat} (F G: functor A B):
  F = G <-> (exists H: F.(map_ob) = G.(map_ob), cast_map_hom_type F G H = @map_hom A B G).
Proof.
  split. { intros Ef. rewrite Ef. exists eq_refl. reflexivity. }
  intros [Eob Ehom]. destruct F as [Fob Fhom Fid Fcomp], G as [Gob Ghom Gid Gcomp].
  simpl in *. destruct Eob. simpl in Ehom. destruct Ehom.
  f_equal; apply proof_irrelevance.
Qed.
