Require Import Morphisms Base Cartesian.

Definition inverse f :=
  comprehension (product (codomain f) (domain f))
  (fun p => exists u, exists v, p ≅ tuple v u /\ tuple u v ∈ f).

Record injection_def (x y : V) (f : V) := {
  injection_def_fun : function_def x y f;
  injection_def_inj : forall u1 u2 v, tuple u1 v ∈ f -> tuple u2 v ∈ f -> u1 ≅ u2
}.

Record bijection_def (x y : V) (f : V) := {
  bijection_def_defl : forall u, u ∈ x -> exists v, v ∈ y /\ (tuple u v) ∈ f;
  bijection_def_defr : forall v, v ∈ y -> exists u, u ∈ x /\ (tuple u v) ∈ f;
  bijection_def_funl : forall u v1 v2, tuple u v1 ∈ f -> tuple u v2 ∈ f -> v1 ≅ v2;
  bijection_def_funr : forall u1 u2 v, tuple u1 v ∈ f -> tuple u2 v ∈ f -> u1 ≅ u2
}.

Definition injection x y := comprehension (powerset (product x y)) (injection_def x y).
Definition bijection x y := comprehension (powerset (product x y)) (bijection_def x y).

Lemma injection_function : forall x y f, injection_def x y f -> function_def x y f.
Proof.
intros x y f [? ?]; assumption.
Qed.

Lemma injection_bijection : forall x y f,
  bijection_def x y f <-> (injection_def x y f /\ injection_def y x (inverse f)).
Proof.
intros x y f.
assert (HP : Proper (V_eq ==> iff) (fun p => exists u, exists v, p ≅ tuple v u /\ tuple u v ∈ f)).
{ apply proper_sym_impl_iff; [apply V_eq_sym|]; intros x1 x2 Hx [u [v H]].
  exists u, v; rewrite <- Hx; assumption. }
split; intros H.
+ destruct H as [Hdefl Hdefr Hfunl Hfunr]; split; split.
  - split; assumption.
  - assumption.
  - split.
    { intros v Hv; destruct (Hdefr v Hv) as [u [Hu Hf]].
      exists u; split; [assumption|].
      apply comprehension_spec; [assumption|].
      split; [|exists u, v; now intuition].
Admitted.
