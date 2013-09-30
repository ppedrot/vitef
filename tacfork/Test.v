Require Fork.

Lemma foo : True /\ True.
Proof.
fork split >> [abstract trivial|trivial].
Qed.

Lemma bar : True /\ True.
Proof.
fork split >> [trivial|admit].
Qed.

Lemma baz : True /\ True.
Proof.
fork split >> [abstract trivial|admit].
Defined.

Goal
  (forall A : Prop, A -> A) /\
  False /\
  (forall A : Prop, False -> A) /\
  (forall A : Prop, A -> A -> A).
Proof.
Time fork (repeat apply conj) >> (intuition eauto).
admit.
Qed.
