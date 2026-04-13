
Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 40, left associativity).
Reserved Infix ";;" (at level 50, left associativity).

Record cat :=
  mk_cat {
      ob: Type;
      hom: ob -> ob -> Type where "a ~> b" := (hom a b);
      comp {a b c: ob}: (a ~> b) -> (b ~> c) -> (a ~> c)
      where "f ∘ g" := (comp g f);

      id {a: ob}: a ~> a;
      id_left {a b: ob} (f: a ~> b): id ∘ f = f;
      id_right {a b: ob} (f: a ~> b): f ∘ id = f;

      assoc {a b c d: ob} (f: a ~> b) (g: b ~> c) (h: c ~> d)
      : h ∘ (g ∘ f) = (h ∘ g) ∘ f;
    }.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Bind Scope cat_scope with cat.

Arguments hom {_}.
Arguments comp {_ _ _ _}.
Arguments id {_ _}.
Notation "a ~> b" := (hom a b): cat_scope.
Notation "f ;; g" := (comp f g): cat_scope.
Notation "f ∘ g" := (comp g f): cat_scope.

Local Open Scope cat_scope.
Check (forall (C: cat) (a b: C.(ob)) (f: a ~> b), True).
Check (fun (C: cat) (a b c: C.(ob)) (f: a ~> b) (g: b ~> c) => g ∘ f).

Definition empty_cat :=
  mk_cat Empty_set (fun _ _ => Empty_set)
    (fun a _ _ _ _ => match a with end)
    (fun a => match a with end)
    (fun a _ _ => match a with end)
    (fun a _ _ => match a with end)
    (fun _ _ _ _ _ _ _ => eq_refl _).

Example empty_cat_ob_id (a b: empty_cat.(ob)): a = b.
Proof. destruct a. Qed.

Example empty_cat_hom_id (a: empty_cat.(ob)) (f: empty_cat.(hom) a a):
  f = empty_cat.(id).
Proof. destruct a. Qed.

Example empty_cat_hom_comp_comm (a: empty_cat.(ob)) (f g: a ~> a):
  f ;; g = g ;; f.
Proof. destruct a. Qed.

Definition empty_cat': cat.
Proof.
  refine {|
      ob := Empty_set;
      hom _ _ := Empty_set;
      comp a _ _ _ _ := match a with end;
    |}; intro a; destruct a.
Defined.

Definition singleton: cat.
Proof.
  refine {|
      ob := unit;
      hom a b := unit;
      comp _ _ _ _ _ := tt;
      id _ := tt;
    |}.
  - (* id_left *) intros. destruct f. reflexivity.
  - (* id_right *) intros. destruct f. reflexivity.
  - (* assoc *) reflexivity.
Qed.

(* left-side inverse *)
Definition inverse {C: cat} {a b: C.(ob)}
  (f: a ~> b) (g: b ~> a): Prop :=
  g ∘ f = id.

Definition isomorphism {C: cat} {a b: C.(ob)} (f: a ~> b): Prop :=
  exists g: b ~> a, inverse f g /\ inverse g f.

Definition epimorphism {C: cat} {a b: C.(ob)} (f: a ~> b): Prop :=
  forall (c: C.(ob)) (g1 g2: b ~> c), g1 ∘ f = g2 ∘ f -> g1 = g2.

Theorem right_inverse_is_epimorphism {C: cat} {a b: C.(ob)} (f: a ~> b):
  (exists (g: b ~> a), inverse g f) -> epimorphism f.
Proof.
  unfold inverse, epimorphism.
  intros [g Hinv] c h1 h2 Heq.
  apply (f_equal (fun f => f ∘ g)) in Heq.
  rewrite <-!C.(assoc) in Heq.
  rewrite Hinv in Heq. rewrite !C.(id_right) in Heq.
  exact Heq.
Qed.

Definition monomorphism {C: cat} {a b: C.(ob)} (f: a ~> b): Prop :=
  forall (c: C.(ob)) (g1 g2: c ~> a), f ∘ g1 = f ∘ g2 -> g1 = g2.

Theorem left_inverse_is_monomorphism {C: cat} {a b: C.(ob)} (f: a ~> b):
  (exists (g: b ~> a), inverse f g) -> monomorphism f.
Proof.
  unfold inverse, monomorphism.
  intros [g Hinv] c h1 h2 Heq.
  apply (f_equal (fun f => g ∘ f)) in Heq.
  rewrite !C.(assoc) in Heq.
  rewrite Hinv in Heq. rewrite !C.(id_left) in Heq.
  exact Heq.
Qed.
