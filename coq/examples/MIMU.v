(* https://t.me/tproger/4921
https://tproger.ru/problems/converting-mi-to-mu

У вас есть строка MI. Выясните, можно ли получить из неё строку MU,
используя только следующие правила:

1. Если строка заканчивается на I, можно добавить в конец U. Пример: MI -> MIU.
2. Можно удвоить часть строки после M, то есть изменить Mx на Mxx. Пример: MIU -> MIUIU.
3. Можно заменить III на U. Пример: MUIIIU -> MUUU.
4. Можно удалить UU. Пример: MUUU -> MU.

Чтобы было проще с этим работать, развернём строчки и уберём бесполезную M:

У вас есть строка I. Выясните, можно ли получить из неё строку U,
используя только следующие правила:

1. Если строка начинается на I, можно добавить в начало U. Пример: I -> UI.
2. Можно удвоить часть строку, то есть изменить x на xx. Пример: IU -> IUIU.
3. Можно заменить III на U. Пример: UIIIU -> UUU.
4. Можно удалить UU. Пример: UUU -> U.
 *)

From Stdlib Require Import Arith Wf_nat List Lia.
Import Nat Peano ListNotations.

Theorem elt_in_not_empty {X: Type} (e: X) (xs ys: list X): xs ++ e :: ys <> [].
Proof.
  destruct xs as [|x xs]; intros H; inversion H.
Qed.

Inductive Char := I | U.
Definition Str := list Char.

Fixpoint countI (s: Str): nat :=
  match s with
  | nil => 0
  | I :: s => S (countI s)
  | U :: s => countI s
  end.

Theorem countI_app (s t: Str): countI (s ++ t) = countI s + countI t.
Proof.
  induction s as [|c s IH]. { reflexivity. }
  simpl. destruct c.
  - (* I *) simpl. rewrite IH. reflexivity.
  - (* U *) exact IH.
Qed.

Fixpoint mult3 (n: nat): bool :=
  match n with
  | 0 => true
  | 1 | 2 => false
  | S (S (S n)) => mult3 n
  end.

Theorem mult3_cycle (n: nat): mult3 (3 + n) = mult3 n.
Proof. reflexivity. Qed.

Theorem mult3_double (n: nat): mult3 (2 * n) = mult3 n.
Proof.
  apply (lt_wf_ind n). clear n.
  intros n IH. destruct n as [| [| [| n]]]; try reflexivity.
  replace (S (S (S n))) with (3 + n) by reflexivity.
  replace (2 * (3 + n)) with (3 + (3 + 2 * n)) by lia.
  rewrite !mult3_cycle. apply IH. lia.
Qed.

Theorem mult3_double' (n: nat): mult3 (n + n) = mult3 n.
Proof.
  replace (n + n) with (2 * n) by lia.
  apply mult3_double.
Qed.

Definition mult3I (s: Str): bool := mult3 (countI s).

Theorem mult3I_consU (s: Str): mult3I (U :: s) = (mult3I s).
Proof. reflexivity. Qed.

Theorem mult3I_double (s: Str): mult3I (s ++ s) = mult3I s.
Proof.
  unfold mult3I. rewrite countI_app. apply mult3_double'.
Qed.

Reserved Notation "s ~> t" (at level 70, no associativity).
Reserved Notation "s ~>> t" (at level 70, no associativity).

Inductive App: Str -> Str -> Prop :=
| R1 (s: Str): (I :: s) ~> (U :: I :: s)
| R2 (s: Str): s ~> (s ++ s)
| R3 (s1 s2: Str): (s1 ++ I :: I :: I :: s2) ~> (s1 ++ U :: s2)
| R4 (s1 s2: Str): (s1 ++ U :: U :: s2) ~> (s1 ++ s2)
where "s ~> t" := (App s t).

Inductive AppN (s: Str): Str -> Prop :=
| AppO: s ~>> s
| AppS (p t: Str): (s ~> p) -> (p ~>> t) -> (s ~>> t)
where "s ~>> t" := (AppN s t).

Lemma App_preserve_mult3I (s t: Str): s ~> t -> mult3I s = mult3I t.
Proof.
  destruct s as [|c s]; intro H.
  - (* [] *) inversion H.
    + (* R2 *) try reflexivity.
    + (* R3 *) contradict H1. clear H H0 t.
      induction s1 as [|c s]; intro H; inversion H.
    + (* R4 *) contradict H1. apply elt_in_not_empty.
  - (* c :: s *) inversion H.
    + (* R1 *) subst s0 c t. rewrite mult3I_consU. reflexivity.
    + (* R2 *) subst s0 t. rewrite mult3I_double. reflexivity.
    + (* R3 *) subst t. unfold mult3I. rewrite !countI_app.
      simpl. rewrite !add_succ_r. reflexivity.
    + (* R4 *) subst t. unfold mult3I. rewrite !countI_app.
      reflexivity.
Qed.

Lemma AppN_preserve_mult3I (s t: Str): s ~>> t -> mult3I s = mult3I t.
Proof.
  intro H. induction H as [s|s p t H0 H IH]. { reflexivity. }
  apply App_preserve_mult3I in H0. rewrite H0. exact IH.
Qed.

Theorem NoU: ~ [I] ~>> [U].
Proof.
  intro H. apply AppN_preserve_mult3I in H as C.
  unfold mult3I in C. simpl in C. discriminate C.
Qed.
