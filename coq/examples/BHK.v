(*** BHK *)
(* https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation *)
(** A proof of P ∧ Q is a pair ⟨a , b⟩
    where a is a proof of P and b is a proof of Q . *)

Print and.
(* Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B. *)

Print pair.
(* Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B. *)

Theorem and_is_pair (A B: Prop): A /\ B <-> A * B.
Proof.
  Check (A * B)%type. split.
  - (* A /\ B -> A * B *)
    intros [HA HB]. exact (HA, HB).
  - (* A * B -> A /\ B *)
    intro H. destruct H as [HA HB]. split.
    + exact HA.
    + exact HB.
Qed.

(** A proof of P ∨ Q is either ⟨0 , a⟩ where a is a proof of P or ⟨1 , b⟩
    where b is a proof of Q . *)

Print or.
(* Inductive or (A B : Prop) : Prop :=
   or_introl : A -> A \/ B | or_intror : B -> A \/ B. *)

Print sum.
(* Inductive sum (A B : Type) : Type :=
   inl : A -> A + B | inr : B -> A + B. *)

Theorem sum_to_or (P Q: Prop): P + Q -> P \/ Q.
Proof.
  intros H. destruct H as [H | H].
  - left. exact H.
  - right. exact H.
Qed.

Theorem or_to_sum (P Q: Prop): P \/ Q -> (P + Q).
Proof.
  intro H. Fail destruct H.
Admitted.  

(** A proof of P → Q is a construction that converts
    a (hypothetical) proof of P into a proof of Q . *)



(** A proof of (∃ x ∈ S) (P x) is a pair ⟨x , a⟩
    where x is an element of S and a is a proof of P x . *)

(** A proof of (∀ x ∈ S) (P x) is a construction that converts
    an element x of S into a proof of P x . *)

(** The formula ¬ P is defined as P → ⊥ , so a proof of it is a construction
    that converts a proof of P into a proof of ⊥ . *)

(** There is no proof of ⊥ , the absurdity. *)
