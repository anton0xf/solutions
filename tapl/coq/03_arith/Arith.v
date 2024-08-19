Require Import Arith.
Require Import List.
Import ListNotations.
Import Nat.

Inductive Term: Set :=
| TTrue
| TFalse
| TZero
| TSucc (t: Term)
| TPred (t: Term)
| TIsZero (t: Term)
| TIf (cond thenBr elseBr: Term).

Example true_neq_false: TTrue <> TFalse.
Proof. discriminate. Qed.

(* def 3.2.3. S_n *)
Fixpoint T (n: nat): list Term :=
  match n with
  | O => []
  | S n' => let T' := T n'
           in [TTrue; TFalse; TZero] ++
                (flat_map (fun t => [TSucc t; TPred t; TIsZero t]) T') ++
                (flat_map (fun t1 => flat_map (fun t2 => map (fun t3 => TIf t1 t2 t3) T') T') T')
  end.

Example true_In_Sn: forall n: nat, n > 0 -> In TTrue (T n).
Proof.
  destruct n as [| n']; intro npos.
  - contradict npos. apply nlt_0_r.
  - simpl. auto.
Qed.

(* ex 3.2.4. size of (T 3) *)
Fixpoint Tlen (n: nat): nat :=
  match n with
  | O => 0
  | S n' => let Tlen' := Tlen n' in 3 + 3 * Tlen' + Tlen'^3 
  end.

Theorem Tlen_is_len_T: forall n: nat, length (T n) = Tlen n.
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - simpl. remember (Tlen n') as Tl eqn:Tl_def.
    remember (T n') as T' eqn:T'_def.
    rewrite length_app.
    assert (length (flat_map (fun t0 : Term => [TSucc t0; TPred t0; TIsZero t0]) T') = Tl * 3) as eq.
    { rewrite flat_map_constant_length with (c := 3).
      - rewrite IH. reflexivity.
      - intros t H. reflexivity.
    } rewrite eq. clear eq.
    assert (length (flat_map (fun t1 : Term => flat_map (fun t2 : Term => map (fun t3 : Term => TIf t1 t2 t3) T') T') T') = Tl^3) as eq.
    { rewrite flat_map_constant_length with (c := Tl^2).
      - rewrite IH. reflexivity.
      - intros t1 H1. rewrite flat_map_constant_length with (c := Tl).
        + rewrite IH. rewrite pow_2_r. reflexivity.
        + intros t2 H2. rewrite length_map. exact IH.
    } rewrite eq. simpl. ring.
Qed.

Compute Tlen 2. (* = 39 : nat *)

Example T3_len: length (T 3) = 3 + 3*39 + 39^3.
Proof. rewrite Tlen_is_len_T. reflexivity. Qed.

(* ex 3.2.5. T is cumulative *)
Theorem incl_flat_map {A: Type} (xs ys: list A) (f: A -> list A):
  incl xs ys -> incl (flat_map f xs) (flat_map f ys).
Proof.
  intro xs_incl_ys. unfold incl. intro fx. repeat rewrite in_flat_map.
  intros [x [x_in_xs H]]. exists x. split.
  - apply xs_incl_ys. exact x_in_xs.
  - exact H.
Qed.

Theorem T_cumulative: forall (n: nat), incl (T n) (T (S n)).
Proof.
  induction n as [| n IH]; intros t H.
  - simpl in H. contradiction.
  - simpl in H. remember (S n) as n1 eqn:n1_def. simpl.
    rewrite in_app_iff. rewrite in_app_iff in H.
    repeat destruct H; try auto.
    + do 3 right. left. apply incl_flat_map with (xs := T n); assumption.
    + do 4 right.
      (* cond *)
      apply incl_flat_map with (xs := T n); try assumption.
      apply in_flat_map in H as [cond [cond_in_Tn H]].
      apply in_flat_map. exists cond. split; try assumption.
      (* thenBr *)
      apply incl_flat_map with (xs := T n); try assumption.
      apply in_flat_map in H as [thenBr [thenBr_in_Tn H]].
      apply in_flat_map. exists thenBr. split; try assumption.
      (* elseBr *)
      apply incl_map with (l1 := T n); assumption. 
Qed.

(* 3.2.6. lim_{n -> inf} (T n) is list of all Term's *)
(* TODO *)

(* TODO The results of evaluation are terms of a particularly simple form: they will
always be either boolean constants or numbers (nested applications of zero
or more instances of succ to 0). Such terms are called values *)
