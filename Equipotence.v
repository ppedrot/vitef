Require Import Base Cartesian.

Definition inverse f :=
  comprehension (product (codomain f) (domain f))
  (fun p => exists u, exists v, p ≅ tuple v u /\ tuple u v ∈ f).

Record injection_def (x y : V) (f : V) := {
  injection_def_fun : function_def x y f;
  injection_def_inj : forall u1 u2 v, u1 ∈ x -> u2 ∈ x -> tuple u1 v ∈ f -> tuple u2 v ∈ f -> u1 ≅ u2
}.

Record bijection_def (x y : V) (f : V) := {
  bijection_def_defl : forall u, u ∈ x -> exists v, v ∈ y /\ (tuple u v) ∈ f;
  bijection_def_defr : forall v, v ∈ y -> exists u, u ∈ x /\ (tuple u v) ∈ f;
  bijection_def_funl : forall u v1 v2, v1 ∈ y -> v2 ∈ y -> tuple u v1 ∈ f -> tuple u v2 ∈ f -> v1 ≅ v2;
  bijection_def_funr : forall u1 u2 v, u1 ∈ x -> u2 ∈ x -> tuple u1 v ∈ f -> tuple u2 v ∈ f -> u1 ≅ u2
}.

Lemma injection_function : forall x y f, injection_def x y f -> function_def x y f.
Proof.
intros x y f [? ?]; assumption.
Qed.

Lemma injection_bijection : forall x y f,
  bijection_def x y f <-> (injection_def x y f /\ injection_def y x (inverse f)).
Proof.
intros x y f; split; intros H.
+ destruct H as [Hdefl Hdefr Hfunl Hfunr]; split; split.
  - split; [assumption|].
    intros u v1 v2 Hu Hv1 Hv2; apply (Hfunl u); try assumption.
Print function_def.

Search