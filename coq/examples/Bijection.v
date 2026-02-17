(* all the definitions came from https://en.wikipedia.org/wiki/Binary_relation *)

(* relation *)
Definition Rel (X Y: Type) := X -> Y -> Prop.

(* functional *)
Definition Fun {X Y: Type} (R: Rel X Y): Prop :=
  forall (x: X) (y1 y2: Y), R x y1 -> R x y2 -> y1 = y2.

Definition Total {X Y: Type} (R: Rel X Y): Prop := forall x: X, exists y: Y, R x y.

(* relation is a function if it is functional and total *)

(* surjective *)
Definition Surj {X Y: Type} (R: Rel X Y): Prop := forall y: Y, exists x: X, R x y.

(* injective *)
Definition Inj {X Y: Type} (R: Rel X Y): Prop :=
  forall (x1 x2: X) (y: Y), R x1 y -> R x2 y -> x1 = x2.

(* bijection *)
Definition Bij {X Y: Type} (f: Rel X Y): Prop := Fun f /\ Total f /\ Surj f /\ Inj f.

(* converse/inverse relation *)
Definition inv {X Y: Type} (R: Rel X Y): Rel Y X :=
  fun (y: Y) (x: X) => R x y.

Theorem Bij_Inv_is_Bij {X Y: Type} (f: Rel X Y): Bij f -> Bij (inv f).
Proof.
  unfold Bij, Fun, Total, Inj, Surj, inv. intros [HFun [HTot [HSurj HInj]]].
  repeat split.
  - (* Fun *) intros y x1 x2 H1 H2. apply HInj with y; assumption.
  - (* Total *) apply HSurj.
  - (* Surj *) apply HTot.
  - (* Inj *) intros y1 y2 x H1 H2. apply HFun with x; assumption.
Qed.

(** Cardinality *)
Require Import Nat List Permutation Lia.
Import ListNotations.

(* list of all elements of X *)
Definition ElemList {X: Type} (xs: list X): Prop := NoDup xs /\ forall x: X, In x xs.

(* finite set *)
Definition Fin (X: Type): Prop := exists xs: list X, ElemList xs.

(* cardinality *)
Definition FinCard (X: Type) (n: nat): Prop :=
  exists xs: list X, ElemList xs /\ length xs = n.

Theorem ElemList_all_same {X: Type} (xs ys: list X):
  ElemList xs -> ElemList ys -> Permutation xs ys.
Proof.
  unfold ElemList. intros [HxND HxIn] [HyND HyIn].
  apply NoDup_Permutation; try assumption.
  intro x. split; intro H.
  - apply HyIn.
  - apply HxIn.
Qed.

Theorem ElemList_forall_iff {X: Type} (P: X -> Prop) (xs: list X) (HE: ElemList xs):
  (forall x: X, P x) <-> (forall x: X, In x xs -> P x).
Proof.
  split; intros H x.
  - intros _ . apply H.
  - apply H. apply HE.
Qed.

Theorem ElemList_exists_iff {X: Type} (P: X -> Prop) (xs: list X) (HE: ElemList xs):
  (exists x: X, P x) <-> (exists x: X, In x xs /\ P x).
Proof.
  split; intros [x H]; exists x.
  - destruct HE as [HND HIn]. split.
    + apply HIn.
    + exact H.
  - apply H.
Qed.

Theorem FinCard_uniq {X: Type} (n m: nat): FinCard X n -> FinCard X m -> n = m.
Proof.
  unfold FinCard. intros [xs [Hx Hn]] [ys [Hy Hm]].
  subst n m. apply Permutation_length.
  apply ElemList_all_same; assumption.
Qed.

Theorem FinCard_empty {X: Type}: (X -> False) -> FinCard X 0.
Proof.
  intro H. exists [].
  split; [|reflexivity].
  split; [constructor|].
  intro x. destruct (H x).
Qed.

Theorem FinCard_zero {X: Type}: FinCard X 0 -> (X -> False).
Proof.
  intros [xs [[_ HIn] HL]].
  apply length_zero_iff_nil in HL. subst xs.
  simpl in HIn. exact HIn.
Qed.

Lemma length_split {X: Type} (x: X) (xs1 xs2: list X):
  length (xs1 ++ x :: xs2) = S (length (xs1 ++ xs2)).
Proof. rewrite !length_app. simpl. lia. Qed.

Lemma list_Bij_same_length {X Y: Type} (f: Rel X Y) (xs: list X) (ys: list Y)
  (HxND: NoDup xs) (HyND: NoDup ys)
  (HFun: forall (x: X) (y1 y2: Y), In x xs -> In y1 ys -> In y2 ys ->
                               f x y1 -> f x y2 -> y1 = y2)
  (HTot: forall x: X, In x xs -> exists y: Y, In y ys /\ f x y)
  (HSurj: forall y: Y, In y ys -> exists x: X, In x xs /\ f x y)
  (HInj: forall (x1 x2: X) (y: Y), In x1 xs -> In x2 xs -> In y ys ->
                               f x1 y -> f x2 y -> x1 = x2):
  length xs = length ys.
Proof.
  generalize dependent ys.
  induction xs as [|x xs IH]; intros ys HyND HFun HTot HSurj HInj.
  { simpl. destruct ys as [|y ys]; [reflexivity|].
    pose (HSurj y (or_introl (eq_refl y))) as H.
    destruct H as [x [[] _]]. }
  pose (HTot x (or_introl (eq_refl x))) as Hy.
  destruct Hy as [y [HyIn Hfy]].
  apply in_split in HyIn as [ys1 [ys2 Hy]]. subst ys.
  pose (NoDup_remove ys1 ys2 y HyND) as Hy.
  destruct Hy as [HyND' NyNIn].
  rewrite length_split. simpl.
  apply eq_S. apply IH; clear IH.
  - (* NoDup xs *) apply NoDup_cons_iff in HxND as [_ HxND]. exact HxND.
  - (* NoDup ys *) exact HyND'.
  - (* Fun *) intros v y1 y2 HvIn Hy1In Hy2In Hf1 Hf2.
    apply (HFun v y1 y2); simpl; auto.
    + apply in_or_app. simpl. apply in_app_or in Hy1In as [H | H]; auto.
    + apply in_or_app. simpl. apply in_app_or in Hy2In as [H | H]; auto.
  - (* Total *) intros v HvIn. pose (HTot v (or_intror HvIn)) as H.
    destruct H as [u [HuIn Hfvu]]. apply in_app_or in HuIn.
    simpl in HuIn. destruct HuIn as [HuIn1 | [Huy | HuIn2]].
    + exists u. split; [|exact Hfvu]. apply in_or_app. left. exact HuIn1.
    + subst u. apply NoDup_cons_iff in HxND as [HxnIn HxND].
      assert (x = v) as Hxv.
      { apply HInj with y; simpl; auto. apply in_elt. }
      subst v. contradiction.
    + exists u. split; [|exact Hfvu]. apply in_or_app. right. exact HuIn2.
  - (* Surj *) intros u HuIn.
    assert (In u (ys1 ++ y :: ys2)) as HuIn'.
    { apply in_app_iff. simpl.
      apply in_app_iff in HuIn as [HIn1 | Hin2]; auto. }
    pose (HSurj u HuIn') as H. destruct H as [v [[Hvx | HvIn] Hfu]].
    + subst v. assert (y = u).
      { apply HFun with x; simpl; auto. apply in_elt. }
      subst u. contradiction.
    + exists v. split; auto.
  - (* Inj *) intros x1 x2 u Hx1In Hx2In HuIn Hf1 Hf2.
    apply (HInj x1 x2 u); simpl; auto.
    apply in_or_app. simpl.
    apply in_app_or in HuIn as [HuIn1 | HuIn2]; auto.
Qed.

(* bijection and cardinality *)
Theorem Bij_same_FinCard (X Y: Type):
  Fin X -> Fin Y -> (exists f: Rel X Y, Bij f) -> exists n: nat, FinCard X n /\ FinCard Y n.
Proof.
  unfold Fin, Bij, Fun, Total, Surj, Inj.
  intros [xs HxE] [ys HyE]
    [f [HFun [HTot [HSurj HInj]]]].
  pose (length xs) as n. exists n. unfold FinCard. split.
  { exists xs. subst n. auto. }
  exists ys. split. { exact HyE. }
  assert (forall (x: X) (y1 y2: Y), In x xs -> In y1 ys -> In y2 ys ->
                               f x y1 -> f x y2 -> y1 = y2) as LFun.
  { rewrite (ElemList_forall_iff _ xs HxE). intros x HxIn.
    rewrite (ElemList_forall_iff _ ys HyE). intros y1 Hy1In.
    rewrite (ElemList_forall_iff _ ys HyE). intros y2 Hy2In.
    intros _ _ _ Hf1 Hf2. apply HFun with x; assumption. }
  assert (forall x: X, In x xs -> exists y: Y, In y ys /\ f x y) as LTot.
  { intros x HIn. rewrite (ElemList_forall_iff _ _ HxE) in HTot.
    apply ElemList_exists_iff; auto. }
  assert (forall y: Y, In y ys -> exists x: X, In x xs /\ f x y) as LSurj.
  { intros y HIn. rewrite (ElemList_forall_iff _ _ HyE) in HSurj.
    apply ElemList_exists_iff; auto. }
  assert (forall (x1 x2: X) (y: Y), In x1 xs -> In x2 xs -> In y ys ->
                               f x1 y -> f x2 y -> x1 = x2) as LInj.
  { rewrite (ElemList_forall_iff _ xs HxE). intros x1 Hx1In.
    rewrite (ElemList_forall_iff _ xs HxE). intros x2 Hx2In.
    rewrite (ElemList_forall_iff _ ys HyE). intros y HyIn.
    intros _ _ _ Hf1 Hf2. apply HInj with y; assumption. }
  clear HFun HTot HSurj HInj. subst n. symmetry.
  apply list_Bij_same_length with f; auto.
  - apply HxE.
  - apply HyE.
Qed.
