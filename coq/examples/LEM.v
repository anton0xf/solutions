Theorem DeMorgan (A B: Prop): ~(A \/ B) -> ~A /\ ~B.
Proof.
  intro H. split; intro C; apply H; [left|right]; exact C.
Qed.

Theorem DN_LEM (A: Prop): ~~(A \/ ~A).
Proof.
  intro H. apply DeMorgan in H. destruct H as [H1 H2].
  apply H2. exact H1.
Qed.

Theorem DN_LEM0 (A: Prop): ~~(A \/ ~A).
Proof. intuition. Qed.

(* https://t.me/c/1062361327/63729
 \nlem. nlem (inr \a -> nlem (inl a))*)
Theorem DN_LEM1 (A: Prop): ~~(A \/ ~A).
Proof.
  intro H.
  apply H. right. intro HA.
  apply H. left. exact HA.
Qed.


  
