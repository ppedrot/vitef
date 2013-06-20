Require Fork.

Goal
  (forall A : Prop, A -> A) /\
  False /\
  (forall A : Prop, False -> A) /\
  (forall A : Prop, A -> A -> A).
Proof.
fork (repeat apply conj) >> (intuition eauto).
admit.
Qed.
