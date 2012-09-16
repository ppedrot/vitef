Require Import Morphisms Base Cartesian.

Definition inverse f :=
  comprehension (product (codomain f) (domain f))
  (fun p => exists u, exists v, p ≅ tuple v u /\ tuple u v ∈ f).

Record injection_def (x y : V) (f : V) := {
  injection_def_def : forall u, u ∈ x -> exists v, v ∈ y /\ tuple u v ∈ f;
  injection_def_fun : forall u v1 v2, tuple u v1 ∈ f -> tuple u v2 ∈ f -> v1 ≅ v2;
  injection_def_inj : forall u1 u2 v, tuple u1 v ∈ f -> tuple u2 v ∈ f -> u1 ≅ u2
}.

Record bijection_def (x y : V) (f : V) := {
  bijection_def_defl : forall u, u ∈ x -> exists v, v ∈ y /\ (tuple u v) ∈ f;
  bijection_def_defr : forall v, v ∈ y -> exists u, u ∈ x /\ (tuple u v) ∈ f;
  bijection_def_funl : forall u v1 v2, tuple u v1 ∈ f -> tuple u v2 ∈ f -> v1 ≅ v2;
  bijection_def_funr : forall u1 u2 v, tuple u1 v ∈ f -> tuple u2 v ∈ f -> u1 ≅ u2
}.

Instance Proper_injection_def : Proper (V_eq ==> V_eq ==> V_eq ==> iff) injection_def.
Proof.
assert (HP : Proper (V_eq ==> V_eq ==> V_eq ==> Basics.impl) injection_def).
{ intros x1 x2 Hx y1 y2 Hy f1 f2 Hf [H1 H2 H3]; split; intros.
  + destruct (H1 u); [rewrite Hx; assumption|]; eexists; rewrite <- Hy, <- Hf; eassumption.
  + eapply H2; rewrite Hf; eassumption.
  + eapply H3; rewrite Hf; eassumption. }
repeat intro; split; apply HP; solve [assumption|symmetry; assumption].
Qed.

Definition injection x y := comprehension (powerset (product x y)) (injection_def x y).
Definition bijection x y := comprehension (powerset (product x y)) (bijection_def x y).

Lemma inverse_spec : forall x y f, tuple x y ∈ f <-> tuple y x ∈ inverse f.
Proof.
intros x y f.
assert (HP : Proper (V_eq ==> iff) (fun p => exists u, exists v, p ≅ tuple v u /\ tuple u v ∈ f)).
{ apply proper_sym_impl_iff; [apply V_eq_sym|]; intros x1 x2 Hx [u [v H]].
  exists u, v; rewrite <- Hx; assumption. }
split; intros H.
+ apply comprehension_spec; [assumption|].
  split; [|exists x, y; split; [reflexivity|assumption]].
  assert (Hmx : singleton x ∈ union f).
  { apply union_spec; exists (tuple x y); split; [|assumption].
    apply pair_spec; left; reflexivity. }
  assert (Hmy : pair x y ∈ union f).
  { apply union_spec; exists (tuple x y); split; [|assumption].
    apply pair_spec; right; reflexivity. }
  assert (Hdx : x ∈ domain f).
  { apply comprehension_spec.
    + intros ? ? ?; repeat f_equiv; assumption.
    + split; [|assumption].
      apply union_spec; exists (singleton x).
      split; [apply singleton_spec; reflexivity|assumption]. }
  assert (Hdy : y ∈ codomain f).
  { apply comprehension_spec.
    + intros ? ? ?; repeat f_equiv; intros ?; repeat f_equiv; assumption.
    + split; [|exists x; intuition].
      apply union_spec; exists (pair x y).
      split; [|assumption]; apply pair_spec; right; reflexivity. }
  apply product_spec; exists y, x; now intuition.
+ apply comprehension_spec in H; [|do 3 intro; do 2 (f_equiv; intro); repeat f_equiv; assumption].
  destruct H as [Hl [u [v [Heq Hf]]]].
  assert (Hrw := tuple_inj_l _ _ _ _ Heq); rewrite <- Hrw in Hf; clear Hrw.
  assert (Hrw := tuple_inj_r _ _ _ _ Heq); rewrite <- Hrw in Hf; clear Hrw.
  assumption.
Qed.

Lemma injection_function : forall x y f, injection_def x y f -> function_def x y f.
Proof.
intros x y f [? ? H]; split; assumption.
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
Admitted.
