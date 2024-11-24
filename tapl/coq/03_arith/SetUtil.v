Require Import MSets MSetWeakList.
Require Import Setoid.

Module SetNotations (X: DecidableType) (XS: WSetsOn X).
  Import XS.
  Declare Scope set_scope.
  Delimit Scope set_scope with t.
  Bind Scope set_scope with t.

  Infix "+:" := add (at level 60, right associativity): set_scope.
  (* Notation "x +: xs" := (add x xs) (at level 60, right associativity). *)
  Notation "{ }" := empty (format "{ }"): set_scope.
  Notation "{ x }" := (add x empty) (format "{ x }"): set_scope.
  Notation "{ x ; .. ; y }" := (add x .. (add y empty) ..)
                                 (format "{ x ; .. ; y }"): set_scope.
  Infix "++" := union (right associativity, at level 60) : set_scope.
  Open Scope set_scope.
End SetNotations.

(** * defs adn facts about set types *)
Module Set1 (X: DecidableType) (XS: WSetsOn X).
  Include XS <+ (WPropertiesOn X XS).
  (* Import XS. *)
  (* Module SetProps := WPropertiesOn X XS. *)
  (* Import SetProps. *)
  (* Export SetProps. *)

  Definition disjoint (s1 s2: XS.t): Prop :=
    forall x: X.t, (In x s1 -> ~In x s2) /\ (In x s2 -> ~In x s1).

  Theorem disjoint_iff_inter_is_empty (s1 s2: XS.t):
    disjoint s1 s2 <-> inter s1 s2 [=] empty.
  Proof.
    unfold disjoint. split; intro H; intro x.
    - destruct (H x) as [H1 H2].
      split; intro G.
      + apply inter_spec in G as [G1 G2].
        apply H1 in G1. contradiction.
      + rewrite FM.empty_iff in G. contradict G.
    - pose (H x) as Hx. rewrite inter_spec in Hx.
      rewrite FM.empty_iff in Hx. rewrite <- neg_false in Hx.
      split; intros G C; apply Hx; split; assumption.
  Qed.

  Theorem cardinal_of_disjoint_union (xs ys: XS.t): disjoint xs ys ->
    cardinal (union xs ys) = cardinal xs + cardinal ys.
  Proof.
    intro HD. rewrite disjoint_iff_inter_is_empty in HD.
    rewrite <- union_inter_cardinal, HD, empty_cardinal.
    apply plus_n_O.
  Qed.
  
  Theorem fold_add' {A: Type} (f: X.t -> A -> A) (x: X.t) (xs xxs: XS.t) (z: A):
    ~In x xs -> Add x xs xxs -> fold f xxs z = f x (fold f xs z).
  Proof.
    intros Nin Hadd. apply Add_Equal in Hadd. repeat rewrite fold_spec_right.
    apply fold_add.
End Set1.

(** * functions on sets and facts about two set types *)
Module Set2 (X Y: DecidableType) (XS: WSetsOn X) (YS: WSetsOn Y).
  Module SetXS := Set1 X XS.
  Module SetYS := Set1 Y YS.
  
  Definition map (f: X.t -> Y.t) (xs: XS.t): YS.t :=
    XS.fold (fun x acc => YS.add (f x) acc) xs YS.empty.

  Definition flat_map (f: X.t -> YS.t) (xs: XS.t): YS.t :=
    XS.fold (fun x acc => YS.union (f x) acc) xs YS.empty.

  Theorem flat_map_of_empty (f: X.t -> YS.t) (xs: XS.t): XS.Empty xs -> flat_map f xs = YS.empty.
  Proof.
    intros Exs. unfold flat_map. rewrite SetXS.fold_1b; try assumption.
    reflexivity.
  Qed.

  Definition disjoint_map (f: X.t -> YS.t) (xs: XS.t) :=
    forall x1 x2: X.t, XS.In x1 xs -> XS.In x2 xs -> x1 <> x2 -> SetYS.disjoint (f x1) (f x2).

  Theorem cardinal_of_disjoint_flat_map (f: X.t -> YS.t) (xs: XS.t):
    disjoint_map f xs ->
    YS.cardinal (flat_map f xs) = XS.fold (fun x acc => YS.cardinal (f x) + acc) xs 0.
  Proof.
    apply SetXS.set_induction with (s := xs); clear xs.
    - intros xs Ex HD. rewrite flat_map_of_empty, SetXS.fold_1b; try assumption.
      rewrite SetYS.cardinal_1; [reflexivity | apply YS.empty_spec].
    - intros xs xxs IH x Nin Hadd HD. 
End Set2.

(* Theorem set_ind (P: set A -> Prop): *)
(*   P empty -> *)
(*   (forall (xs: set A) (x: A), P xs -> P (add x xs)) -> *)
(*   forall xs: set A, P xs. *)
(* Proof. *)
(*   subst empty add union. *)
(* Theorem union_empty_r (xs: set A): union xs empty = xs. *)
(* Proof. reflexivity. Qed. *)

(* Theorem union_empty_l (xs: set A): union empty xs = xs. *)
(* Proof. *)
(*   induction xs as [|x xs IH]; try reflexivity. *)
(*   simpl. rewrite IH.  *)

(* Theorem union_sym (xs ys: set A): union xs ys = union ys xs. *)
(* Proof.  *)
(*   generalize dependent xs. *)
(*   induction ys as [|y ys IH]; intros xs. *)
(*   - simpl. *)

(* Theorem union_size (xs ys: set A): *)
(*   set_size (set_union Aeq_dec xs ys) *)
(*   = set_size xs + set_size ys - set_size (set_inter Aeq_dec xs ys). *)
(* Proof. *)
(*   generalize dependent ys. *)
(*   induction xs as [|x xs IH]; intro ys. *)
(*   - simpl. *)

(*  app_length (* length_app *). *)

