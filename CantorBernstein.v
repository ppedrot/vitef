Require Import Base Cartesian.

Section CantorBernstein.

Variable E : V.
Variable F : V.
Variable F_function : F ∈ function (powerset E) (powerset E).
Variable F_growing : forall p1 p2, p1 ∈ powerset E -> p2 ∈ powerset E -> p1 ⊆ p2 ->
  app F p1 ⊆ app F p2.

Let D := comprehension (powerset E) (fun p => p ⊆ app F p).

Definition Φ := union D.

Lemma Φ_defined : Φ ∈ powerset E.
Proof.
apply powerset_spec; apply included_spec; intros x Hx.
apply union_spec in Hx; destruct Hx as [y [Hx Hy]].
apply comprehension_spec in Hy; [|clear; intros x1 x2 Hx; rewrite Hx; reflexivity].
destruct Hy as [Hy HF].
apply powerset_spec in Hy; eapply mem_included_compat; eassumption.
Qed.

Lemma D_stable : forall p, p ∈ D -> app F p ∈ D.
Proof.
intros p Hp.
apply comprehension_spec in Hp; [|intros x1 x2 Hx; rewrite Hx; reflexivity].
destruct Hp as [Hpl Hpr].
apply comprehension_spec; [intros x1 x2 Hx; rewrite Hx; reflexivity|].
split; [eapply app_defined; eassumption|].
apply F_growing; try assumption.
eapply app_defined; eassumption.
Qed.

Lemma Φ_sup : forall p, p ∈ D -> app F p ⊆ Φ.
Proof.
intros p Hp; apply included_spec; intros z Hz.
apply union_spec; exists (app F p); split; [assumption|].
apply D_stable; assumption.
Qed.

Lemma Φ_bounded : Φ ∈ D.
Proof.
apply comprehension_spec; [intros x1 x2 Hx; rewrite Hx; reflexivity|].
split; [apply Φ_defined|].
apply included_spec; intros z Hz.
apply union_spec in Hz; destruct Hz as [φ [Hz Hφ]].
eapply mem_included_compat; [eassumption|].
transitivity (app F φ).
{ apply comprehension_spec in Hφ; [intuition|intros x1 x2 Hx; rewrite Hx; reflexivity]. }
transitivity (app F (app F φ)).
{ apply D_stable in Hφ; apply comprehension_spec in Hφ; [intuition|intros x1 x2 Hx; rewrite Hx; reflexivity]. }
apply F_growing.
+ eapply app_defined; [eexact F_function|].
  apply comprehension_spec in Hφ; [intuition|intros x1 x2 Hx; rewrite Hx; reflexivity].
+ apply Φ_defined.
+ apply Φ_sup; assumption.
Qed.

Lemma Φ_fixpoint : app F Φ ≅ Φ.
Proof.
apply extensionality.
+ apply Φ_sup; apply Φ_bounded.
+ pose (H := Φ_bounded).
  apply comprehension_spec in H; [|intros x1 x2 Hx; rewrite Hx; reflexivity].
  now intuition.
Qed.

End CantorBernstein.
