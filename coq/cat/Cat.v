
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

Arguments hom {c0}.
Arguments comp {c0 a b c}.
Arguments id {c0 a}.
Arguments id_left {c0 a b}.
Arguments id_right {c0 a b}.
Arguments assoc {c0 a b c d}.

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

Theorem inverse_comp {C: cat} {a b c: C.(ob)}
  (f: a ~> b) (f': b ~> a) (g: b ~> c) (g': c ~> b):
  inverse f f' -> inverse g g' -> inverse (f ;; g) (g' ;; f').
Proof.
  unfold inverse. intros H1 H2.
  rewrite <- assoc, (assoc _ _ g'). rewrite H2.
  rewrite id_left. exact H1.
Qed.

Definition inversion {C: cat} {a b: C.(ob)}
  (f: a ~> b) (g: b ~> a): Prop :=
  inverse f g /\ inverse g f.

Theorem inversion_sym {C: cat} {a b: C.(ob)} (f: a ~> b) (g: b ~> a):
  inversion f g -> inversion g f.
Proof. unfold inversion. intuition. Qed.

Theorem inversion_uniq {C: cat} {a b: C.(ob)}
  (f: a ~> b) (g1 g2: b ~> a):
  inversion f g1 -> inversion f g2 -> g1 = g2.
Proof.
  unfold inversion, inverse. intros [Hl1 Hr1] [Hl2 Hr2].
  rewrite <- (id_left g1), <- Hl2, <- assoc.
  rewrite Hr1, id_right. reflexivity.
Qed.

Theorem inversion_comp {C: cat} {a b c: C.(ob)}
  (f: a ~> b) (f': b ~> a) (g: b ~> c) (g': c ~> b):
  inversion f f' -> inversion g g' -> inversion (f ;; g) (g' ;; f').
Proof.
  unfold inversion. intros [Hf Hf'] [Hg Hg'].
  split; apply inverse_comp; assumption.
Qed.

Definition isomorphism {C: cat} {a b: C.(ob)} (f: a ~> b): Prop :=
  exists g: b ~> a, inversion f g.

Definition isomorphic {C: cat} (a b: C.(ob)): Prop := exists f: a ~> b, isomorphism f.

Notation "a ~~ b" := (isomorphic a b) (at level 70, no associativity).

Theorem isomorphic_refl {C: cat} (a: C.(ob)): a ~~ a.
Proof. exists id, id. split; unfold inverse; apply C.(id_left). Qed.

Theorem isomorphic_sym {C: cat} (a b: C.(ob)): a ~~ b -> b ~~ a.
Proof.
  unfold isomorphic, isomorphism.
  intros [f [g H]]. exists g, f. apply inversion_sym. exact H.
Qed.

Theorem isomorphic_trans {C: cat} (a b c: C.(ob)): a ~~ b -> b ~~ c -> a ~~ c.
Proof.
  intros [f [f' H1]] [g [g' H2]].
  exists (f ;; g), (g' ;; f').
  apply inversion_comp; assumption.
Qed.

Definition uniq_up_to_isomorphism {C: cat} (P: C.(ob) -> Prop) (x: C.(ob)) :=
  P x /\ forall y, P y -> x ~~ y.
  
Definition epimorphism {C: cat} {a b: C.(ob)} (f: a ~> b): Prop :=
  forall (c: C.(ob)) (g1 g2: b ~> c), g1 ∘ f = g2 ∘ f -> g1 = g2.

Theorem right_inverse_is_epimorphism {C: cat} {a b: C.(ob)} (f: a ~> b):
  (exists (g: b ~> a), inverse g f) -> epimorphism f.
Proof.
  unfold inverse, epimorphism.
  intros [g Hinv] c h1 h2 Heq.
  apply (f_equal (fun f => f ∘ g)) in Heq.
  rewrite <-!assoc in Heq.
  rewrite Hinv in Heq. rewrite !id_right in Heq.
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
  rewrite !assoc in Heq.
  rewrite Hinv in Heq. rewrite !C.(id_left) in Heq.
  exact Heq.
Qed.

Definition terminal {C: cat} (x: C.(ob)): Prop := forall y: C.(ob), exists! f: y ~> x, True.

Theorem terminal_id {C: cat} (x: C.(ob)): terminal x -> forall f: x ~> x, f = id.
Proof. 
  intros Ht f. pose (Ht x) as H. destruct H as [g [_ H]].
  apply eq_trans with g; [symmetry|]; apply H; exact I.
Qed.

Theorem terminal_uniq_up_to_isomorphism {C: cat} (x: C.(ob)):
  terminal x -> uniq_up_to_isomorphism terminal x.
Proof.
  unfold uniq_up_to_isomorphism. intro Hx.
  split; [exact Hx|]. intros y Hy.
  unfold isomorphic, isomorphism.
  pose (Hx y) as Hxy. pose (Hy x) as Hyx.
  destruct Hxy as [g [_ Hxy]], Hyx as [f [_ Hyx]].
  exists f, g. unfold inversion, inverse.
  split; apply terminal_id; assumption.
Qed.

Definition initial {C: cat} (x: C.(ob)): Prop := forall y: C.(ob), exists! f: x ~> y, True.

Theorem initial_id {C: cat} (x: C.(ob)): initial x -> forall f: x ~> x, f = id.
Proof. 
  intros Hi f. pose (Hi x) as H. destruct H as [g [_ H]].
  apply eq_trans with g; [symmetry|]; apply H; exact I.
Qed.

(* TODO
   - D initial object
   - D oposite cat
   - T initial object is oposite to terminal
   - T oposite cat is inversion (functor?)
   - D (co)product

   - pre-order, partial order and total order cats
 *)
