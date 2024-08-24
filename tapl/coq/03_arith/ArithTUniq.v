Require Import TAPL_03_Arith.Arith.
Require Import Arith.Arith.
Require Import List.
Import ListNotations.
Import Nat.
Import Basics.
Require Import Permutation.

(* all elements of (T n) are uniq *)

Theorem flat_map_fs_cons_perm {A B: Type} (g: A -> B) (h: A -> list B) (xs: list A):
  Permutation
    (flat_map (fun x => g x :: h x) xs)
    (map g xs ++ flat_map h xs).
Proof.
  induction xs as [| x xs IH].
  - simpl. reflexivity.
  - simpl. apply perm_skip. apply perm_trans with (l' := h x ++ map g xs ++ flat_map h xs).
    + apply Permutation_app_head. exact IH.
    + rewrite Permutation_app_swap_app. reflexivity.
Qed.

Theorem flat_map_fs_concat_map_perm {A B: Type} (fs: list (A -> B)) (xs: list A):
  Permutation
    (flat_map (fun x => map (fun f => f x) fs) xs)
    (concat (map (fun f => map f xs) fs)).
Proof.
  rewrite <- flat_map_concat_map.
  induction fs as [|g fs IHf]; simpl.
  - induction xs as [| x xs IHx]; try reflexivity. simpl. apply IHx.
  - remember (fun f => map f xs) as F eqn:F_def.
    remember (fun x => map (fun f => f x) fs) as h eqn:h_def.
    apply Permutation_trans with (l' := map g xs ++ flat_map h xs).
    + subst h. apply flat_map_fs_cons_perm.
    + apply Permutation_app_head. apply IHf.
Qed.

Theorem NoDup_app_iff {A: Type} (xs ys: list A):
  NoDup (xs ++ ys) <-> NoDup xs /\ NoDup ys /\ forall x, In x xs -> ~(In x ys).
Proof.
  induction xs as [|x xs IH]; simpl.
  - split; intro H; try intuition. apply NoDup_nil.
  - split; intro H.
    + apply NoDup_cons_iff in H as [x_nin H].
      rewrite in_app_iff in x_nin.
      apply Decidable.not_or in x_nin as [x_nin_xs x_nin_ys].
      apply IH in H. destruct H as [NDxs [NDys H]]. repeat split; try assumption.
      * apply NoDup_cons; assumption.
      * intros y [y_eq | y_in].
        { subst y. apply x_nin_ys. }
        { apply H, y_in. }
    + destruct H as [NDx_xs [Ndys H]].
      apply NoDup_cons_iff in NDx_xs as [x_nin_xs NDxs].
      apply NoDup_cons.
      * rewrite in_app_iff. intros [x_in_xs | x_in_ys]; try contradiction.
        apply (H x); try assumption. left. reflexivity.
      * apply IH. repeat split; try assumption.
        intros y y_in_xs y_in_ys. apply (H y); try exact y_in_ys.
        right. exact y_in_xs.
Qed.

Definition Injective {A B} (f: A -> B) := forall x y, f x = f y -> x = y.

Theorem NoDup_map_injective {A B: Type} (f: A -> B) (xs: list A):
  NoDup xs -> Injective f -> NoDup (map f xs).
Proof.
  induction xs as [|x xs IH].
  - simpl. intros _ _. apply NoDup_nil.
  - intros ND Inj. simpl. apply NoDup_cons_iff in ND as [x_nin ND].
    apply NoDup_cons.
    + intro C. apply in_map_iff in C as [y [eq y_in]].
      apply Inj in eq. subst y. contradiction.
    + apply IH; assumption.
Qed.

Definition Disjoint_multimap {A B: Type} (f : A -> list B) :=
  (forall x: A, NoDup (f x)) /\
    forall x1 x2: A, (exists y: B, In y (f x1) /\ In y (f x2)) -> x1 = x2.

Theorem NoDup_flat_map_disjoint {A B: Type} (f: A -> list B) (xs: list A):
  NoDup xs -> Disjoint_multimap f -> NoDup (flat_map f xs).
Proof.
  induction xs as [|x xs IH].
  - simpl. intros _ _. apply NoDup_nil.
  - intros ND Dis. apply NoDup_cons_iff in ND as [x_nin ND].
    simpl. rewrite NoDup_app_iff. inversion Dis as [NDf D] . repeat split.
    + apply NDf.
    + apply IH. exact ND. exact Dis.
    + intros y y_in C. apply in_flat_map in C as [z [z_in C]].
      assert (x = z) as eq. { apply (D x z). exists y. split; [exact y_in | exact C]. }
      subst x. contradiction.
Qed.

Theorem T_uniq (n: nat): NoDup (T n).
Proof.
  induction n as [|n IH]. { simpl. apply NoDup_nil. }
  simpl. repeat apply NoDup_cons.
  - intro H. apply in_inv in H as [H | H]. { inversion H. }
    apply in_inv in H as [H | H]. { inversion H. }
    apply in_app_or in H as [H | H].
    + apply in_flat_map in H as [t [_ H]].
      apply in_inv in H as [H | H]. { inversion H. }
      apply in_inv in H as [H | H]. { inversion H. }
      apply in_inv in H as [H | H]. { inversion H. }
      contradict H.
    + apply in_flat_map in H as [t1 [_ H]].
      apply in_flat_map in H as [t2 [_ H]].
      apply in_map_iff in H as [t3 [H _]].
      inversion H.
  - intro H. apply in_inv in H as [H | H]. { inversion H. }
    apply in_app_or in H as [H | H].
    + apply in_flat_map in H as [t [_ H]].
      apply in_inv in H as [H | H]. { inversion H. }
      apply in_inv in H as [H | H]. { inversion H. }
      apply in_inv in H as [H | H]. { inversion H. }
      contradict H.
    + apply in_flat_map in H as [t1 [_ H]].
      apply in_flat_map in H as [t2 [_ H]].
      apply in_map_iff in H as [t3 [H _]].
      inversion H.
  - intro H. apply in_app_or in H as [H | H].
    + apply in_flat_map in H as [t [_ H]].
      apply in_inv in H as [H | H]. { inversion H. }
      apply in_inv in H as [H | H]. { inversion H. }
      apply in_inv in H as [H | H]. { inversion H. }
      contradict H.
    + apply in_flat_map in H as [t1 [_ H]].
      apply in_flat_map in H as [t2 [_ H]].
      apply in_map_iff in H as [t3 [H _]].
      inversion H.
  - pose (flat_map_fs_concat_map_perm [TSucc; TPred; TIsZero] (T n)) as perm.
    simpl in perm. rewrite app_nil_r in perm. apply Permutation_sym in perm.
    assert (NoDup (map TSucc (T n))) as L1.
    { apply NoDup_map_injective. exact IH. intros x y eqf. inversion eqf. reflexivity. }
    assert (NoDup (map TPred (T n))) as L2.
    { apply NoDup_map_injective. exact IH. intros x y eqf. inversion eqf. reflexivity. }
    assert (NoDup (map TIsZero (T n))) as L3.
    { apply NoDup_map_injective. exact IH. intros x y eqf. inversion eqf. reflexivity. }
    assert (NoDup (map TPred (T n) ++ map TIsZero (T n))) as L23.
    { apply NoDup_app_iff. repeat split; try assumption. intros t H C.
      apply in_map_iff in H as [t1 [eqh H]].
      apply in_map_iff in C as [t2 [eqc C]].
      subst t. inversion eqc. }
    apply NoDup_app_iff. repeat split.
    + apply (Permutation_NoDup perm).
      apply NoDup_app_iff. repeat split; try assumption. intros t H C.
      apply in_map_iff in H as [t1 [eqh H]].
      apply in_app_or in C as [C|C].
      * apply in_map_iff in C as [t2 [eqc C]]. subst t. inversion eqc.
      * apply in_map_iff in C as [t2 [eqc C]]. subst t. inversion eqc.
    + apply NoDup_flat_map_disjoint; try assumption. split.
      * intro t1. apply NoDup_flat_map_disjoint; try assumption. split.
        { intro t2. apply NoDup_map_injective; try assumption.
          intros t3a t3b H. inversion H. reflexivity. }
        intros t2a t2b [y [y_ina y_inb]].
        apply in_map_iff in y_ina as [t3a [y_def_a t3a_in]].
        apply in_map_iff in y_inb as [t3b [y_def_b t3b_in]].
        subst y. inversion y_def_b. reflexivity.
      * intros t1a t1b [y [y_ina y_inb]].
        apply in_flat_map in y_ina as [t2a [t2a_in y_ina]].
        apply in_map_iff in y_ina as [t3a [y_def_a t3a_in]].
        apply in_flat_map in y_inb as [t2b [t2b_in y_inb]].
        apply in_map_iff in y_inb as [t3b [y_def_b t3b_in]].
        subst y. inversion y_def_b. reflexivity.
    + intros t H C.
      apply in_flat_map in C as [t1 [t1_in C]].
      apply in_flat_map in C as [t2 [t2_in C]].
      apply in_map_iff in C as [t3 [C t3_in]].
      subst t. apply in_flat_map in H as [t0 [t0_in H]]. simpl in H.
      destruct H as [H | [H | [H | H]]]; inversion H.
Qed.
