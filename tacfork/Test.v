Require Fork.

Goal True /\ True.
Proof.
Time fork split >> [trivial|trivial].
Qed.

Goal
  (forall A : Prop, A -> A) /\
  False /\
  (forall A : Prop, False -> A) /\
  (forall A : Prop, A -> A -> A).
Proof.
Time fork (repeat apply conj) >> (intuition eauto).
admit.
Qed.
