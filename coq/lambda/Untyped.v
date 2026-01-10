(* https://en.wikipedia.org/wiki/Lambda_calculus *)
Require Import Bool Arith String List
  OrdersEx MSetWeakList MSetProperties
  Relation_Definitions.
Import Nat ListNotations Ascii.

(** Lambda expression *)
(* 𝑒 ::= 𝑥 ∣ 𝜆⁢𝑥.𝑒 ∣⁢ 𝑒𝑒 *)
Inductive LExpr :=
| LVar (name: string) 
| LApp (M N: LExpr)
| L (var: string) (body: LExpr).

(** short syntax *)
Open Scope string_scope.

(* see https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html#lab403 for details *)
Coercion LVar : string >-> LExpr.

Declare Custom Entry lam.

Notation "<{ x }>" := x (x custom lam).
Notation "( x )" := x (in custom lam, x at level 99).
Notation "x" := x (in custom lam at level 0, x constr at level 0).
Notation "x => y" := (L x y) (in custom lam at level 95, right associativity).
Notation "x y" := (LApp x y) (in custom lam at level 80, left associativity).

Definition x: string := "x".
Definition y: string := "y".
Definition z: string := "z".
Definition f: string := "f".
Definition g: string := "g".

Check <{ (x => x x) y }>.

Unset Printing Notations.
Check <{ (x => x x) y }>.
Set Printing Notations.

(** Set of strings *)
Definition strs := string -> Prop.
Definition empty_str: strs := fun x => False.
Definition add_str (x: string) (A: strs): strs := fun y => x = y \/ A y.
Axiom strs_eq: forall A B: strs, A = B <-> forall x, A x <-> B x.
Definition strs_union (A B: strs): strs := fun x => A x \/ B x.
Definition remove_str (x: string) (A: strs): strs := fun y => y <> x /\ A y.

Notation "{{ }}" := empty_str.
Notation "{{ x ; .. ; y }}" := (add_str x .. (add_str y empty_str) ..).

Check {{ "a"; "b"; "c" }}.

(** Free variables of Lambda expression *)
Fixpoint free_vars (M: LExpr): strs :=
  match M with
  | LVar name => {{ name }}
  | LApp M N => strs_union (free_vars M) (free_vars N)
  | L var body => remove_str var (free_vars body)
  end.

Example free_vars_ex: free_vars <{ (x => z x) y }> = {{ z; y }}.
Proof.
  simpl. apply strs_eq. intro t.
  unfold strs_union, remove_str, add_str, empty_str.
  split; intro H.
  - destruct H as [[neq [[eq | []] | [eq | []]]] | [eq | []]].
    + subst t. left. reflexivity.
    + subst t. contradict neq. reflexivity.
    + subst t. right. left. reflexivity.
  - destruct H as [eqz | [eqy | []]].
    + subst t. left. split. discriminate.
      left. left. reflexivity.
    + subst t. right. left. reflexivity.
Qed.

(** option helpers *)
(* fmap / <$>
   https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Prelude.html#v:fmap
   https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Prelude.html#v:-60--36--62- *)
Definition opt_fmap {A B: Type} (f: A -> B) (x: option A): option B :=
  match x with
  | Some x => Some (f x)
  | None => None
  end.
Notation "f <$> x" := (opt_fmap f x) (at level 55, left associativity).

(* ap / <*>
   https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Control-Monad.html#v:ap
   https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Prelude.html#v:-60--42--62- *)
Definition opt_ap {A B: Type} (f: option (A -> B)) (x: option A): option B :=
  match f, x with
  | Some f, Some x => Some (f x)
  | _, _ => None
  end.
Notation "f <*> x" := (opt_ap f x) (at level 55, left associativity).

Check pair <$> (Some 1) <*> (Some false) : option (nat * bool).
Compute pair <$> (Some 1) <*> (Some false). (* = Some (1, false) *)


(** substitution *)
(* The notation 𝑀⁡[𝑥:=𝑁] denotes capture-avoiding substitution:
substituting N for every free occurrence of x in M,
while avoiding variable capture. *)

Fixpoint try_subst (x: string) (M N: LExpr): option LExpr :=
  match M with
  | LVar name => Some (if name =? x then N else M)
  | LApp A B => LApp <$> try_subst x A N <*> try_subst x B N
  | L var body => if var =? x then Some M else
                   if strs_mem var (free_vars N) then None
                   else L var <$> try_subst x body N
  end.

Example try_subst_var_ex0: try_subst x y z = Some (LVar y).
Proof. reflexivity. Qed.

Example try_subst_var_ex1: try_subst x x z = Some (LVar z).
Proof. reflexivity. Qed.

Example try_subst_L_ex0: try_subst x <{ x => f y }> z = Some <{ x => f y }>.
Proof. reflexivity. Qed.

Example try_subst_L_ex1: try_subst x <{ y => f y }> <{ g y }> = None.
Proof. reflexivity. Qed.

Example try_subst_L_ex2: try_subst x <{ y => f x y }> z = Some <{ y => f z y }>.
Proof. reflexivity. Qed.

Example try_subst_ex:
  try_subst x <{ (y => f x y) (g x) }> z = Some <{ (y => f z y) (g z) }>.
Proof. reflexivity. Qed.

Reserved Notation "M [ x := Y ]> N" (at level 5, no associativity).

Inductive subst: string -> LExpr -> LExpr -> LExpr -> Prop :=
| subst_same_var (x: string) (Y: LExpr): x [x := Y]> Y
| subst_other_var (x m: string) (Y: LExpr): m <> x -> m [x := Y]> m
| subst_app (x: string) (A B Y A' B': LExpr):
  A [x := Y]> A' -> B [x := Y]> B' -> <{ A B }> [x := Y]> <{ A' B' }>
| subst_L_same_var (x: string) (M Y: LExpr): <{ x => M }> [x := Y]> <{ x => M }>
| subst_L_other_var (x t: string) (M Y N: LExpr):
  t <> x -> ~ strs_In t (free_vars Y)
  -> M [x := Y]> N -> <{ t => M }> [x := Y]> <{ t => N }>
where "M [ x := Y ]> N" := (subst x M Y N).

Check <{ f x }> [ x := y ]> <{ f y }>.

Theorem subst_correct (x: string) (M N M': LExpr):
  subst x M N M' <-> match try_subst x M N with
                   | None => False
                   | Some U => U = M'
                   end.
Proof.
  split.
  - (* -> *) intro H.
    induction H as [x N | x y N neq
                   | x A B N A' B' HA IHA HB IHB
                   | x M N | x y M N M' neq nIn H IH].
    + simpl. rewrite String.eqb_refl. reflexivity.
    + simpl. apply String.eqb_neq in neq. rewrite neq. reflexivity.
    + simpl. destruct (try_subst x A N) as [A''|] eqn:eqA.
      2: { destruct IHA. } subst A''.
      destruct (try_subst x B N) as [B''|] eqn:eqB.
      2: { destruct IHB. } subst B''.
      simpl. reflexivity.
    + simpl. rewrite String.eqb_refl. reflexivity.
    + simpl. apply String.eqb_neq in neq. rewrite neq.
      destruct (strs_mem_reflect_In y (free_vars N)). { contradiction. }
      clear n. destruct (try_subst x M N) as [U|].
      2: { destruct IH. } subst U.
      simpl. reflexivity.
  - (* <- *) generalize dependent M'.
    induction M as [y | A IHA B IHB | y B IH]; intro M'.
    + simpl. destruct (String.eqb_spec y x) as [eq|neq].
      * subst y. intro eq. subst M'. apply subst_same_var.
      * intro eq. subst M'. apply subst_other_var. exact neq.
    + simpl. destruct (try_subst x A N) as [A'|] eqn:eqA.
      2: { simpl. contradiction. }
      destruct (try_subst x B N) as [B'|] eqn:eqB.
      2: { simpl. contradiction. }
      simpl. intro eqM. subst M'. apply subst_app.
      * apply IHA. reflexivity.
      * apply IHB. reflexivity.
    + simpl. destruct (String.eqb_spec y x) as [eq|neq].
      { intro eqM. subst x M'. apply subst_L_same_var. }
      destruct (strs_mem_reflect_In y (free_vars N)) as [HIn|HnIn].
      { contradiction. }
      destruct (try_subst x B N) as [B'|].
      2: { simpl.  contradiction. }
      simpl. intro eqM. subst M'. apply subst_L_other_var; try assumption.
      apply IH. reflexivity.
Qed.



Theorem subst_var_sym (u v: string) (A B: LExpr):
  ~ strs_In v (free_vars A)
  -> A [u := v]> B -> B [v := u]> A.
Proof.
  intros nIn_v_A H. remember (LVar v) as Y eqn:eqv.
  induction H as [u V | u y v' neq_yu | u A1 A2 v' A1' A2' H1 IH1 H2 IH2
                 | u M v' | u y M v' M' neq nIn H IH].
  - subst V. apply subst_same_var.
  - subst v'. apply subst_other_var. simpl in nIn_v_A.
    apply Decidable.not_or in nIn_v_A as [neq_yv _].
    exact neq_yv.
  - subst v'.
    simpl in nIn_v_A. rewrite strs_union_iff in nIn_v_A.
    apply Decidable.not_or in nIn_v_A as [nIn_v_A1 nIn_v_A2].
    apply subst_app.
    + apply IH1; [assumption | reflexivity].
    + apply IH2; [assumption | reflexivity].
  - subst v'. simpl in nIn_v_A.
    
    destruct (String.eqb_spec u v) as [eq|neq].
    + subst v. apply subst_L_same_var.
    + apply subst_L_other_var.
      * exact neq.
      * admit.
      * 

    inversion H.
  - apply subst_correct. simpl. rewrite String.eqb_refl. reflexivity.
  - subst x0 A B Y. simpl in nIn_v_A.
    apply Decidable.not_or in nIn_v_A as [neq _].
    apply subst_other_var. exact neq.
  - subst A B x0 Y.

Admitted.

(** α-conversion *)
Inductive a_conv: LExpr -> LExpr -> Prop :=
| a_conv_same_var (x: string): a_conv x x
| a_conv_L (x y: string) (A B: LExpr): subst x A y B -> a_conv <{ x => A }> <{ y => B }>
| a_conv_in_L (x: string) (A B: LExpr): a_conv A B -> a_conv <{ x => A }> <{ x => B }>
| a_conv_app_l (A A' B: LExpr): a_conv A A' -> a_conv <{ A B }> <{ A' B }>
| a_conv_app_r (A B B': LExpr): a_conv B B' -> a_conv <{ A B }> <{ A B' }>.

Theorem a_conv_refl: reflexive LExpr a_conv.
Proof.
  unfold reflexive. intro e. induction e as [x | M IHM N IHN | x M IH].
  - apply a_conv_same_var.
  - apply a_conv_app_l. apply IHM.
  - apply a_conv_in_L. apply IH.
Qed.

Theorem a_conv_sym: symmetric LExpr a_conv.
Proof.
  unfold symmetric. intros u v H.
  induction H as [x | x y A B H | x A B H IH | A A' B H IH | A B B' H IH].
  - apply a_conv_same_var.
  - apply a_conv_L. admit.
  - apply a_conv_in_L. exact IH.
  - apply a_conv_app_l. exact IH.
  - apply a_conv_app_r. exact IH.
Qed.

Theorem a_conv_equiv: equiv LExpr a_conv.
Proof.
  repeat split.
  - 
  - 
  - 
