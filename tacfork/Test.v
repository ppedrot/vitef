Require Fork.

Goal
  (forall A : Prop, A -> A) /\
  False /\
  (forall A : Prop, False -> A) /\
  (forall A : Prop, A -> A -> A).
Proof.
repeat apply conj; fork idtac >> intuition eauto.
admit.
Qed.
