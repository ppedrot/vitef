Require Import Base Cartesian Equipotence.

Section Tarski.

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

End Tarski.

Section CantorBernstein.

Variable A B : V.
Variable f g : V.

Variable f_inj : f ∈ injection A B.
Variable g_inj : g ∈ injection B A.

Let sub x y := comprehension x (fun z => ~ z ∈ y).
Let img f x := collection x (app f).

Definition F := reify (powerset A) (fun X => sub A (img g (sub B (img f X)))).

Let sub_spec : forall x y z, z ∈ sub x y <-> (z ∈ x /\ ~ z ∈ y).
Proof.
intros x y z; split; intros H.
+ apply comprehension_spec in H; [|intros x1 x2 Hx; rewrite Hx; reflexivity].
  assumption.
+ apply comprehension_spec; [intros x1 x2 Hx; rewrite Hx; reflexivity|].
  assumption.
Qed.

Let img_spec : forall f x z, z ∈ img f x <-> (exists u, u ∈ x /\ app f u ≅ z).
Proof.
Admitted.

(* Lemma F_spec : forall X x, X ∈ powerset A ->
  (x ∈ app F X) <->
    (x ∈ A /\
    (forall y, y ∈ B -> (forall z, z ∈ X -> ~ tuple z y ∈ f) -> ~ tuple y x ∈ g)). *)

Lemma F_growing : forall X Y, X ∈ powerset A -> Y ∈ powerset A -> X ⊆ Y -> app F X ⊆ app F Y.
Proof.
intros X Y HX HY Hm; apply included_spec; intros z Hz.
unfold F in *; rewrite reify_spec; [|admit|assumption].
rewrite reify_spec in Hz; [|admit|assumption].
apply sub_spec; apply sub_spec in Hz; destruct Hz as [He Hz]; split; [intuition|intros Hc].
apply Hz; clear Hz.
apply img_spec; apply img_spec in Hc; destruct Hc as [u [Hul Hur]].
exists u; split; [|assumption].
apply sub_spec; apply sub_spec in Hul; split; [now intuition|].
destruct Hul as [Hu Hz]; intros Hc; apply Hz; clear Hz.
apply img_spec; apply img_spec in Hc; destruct Hc as [v Hv].
exists v; split; [|intuition].
eapply mem_included_compat; [|eassumption]; intuition.
Qed.

Lemma F_defined : F ∈ function (powerset A) (powerset A).
Proof.
eapply codomain_included_compat; [apply reify_defined|].
Admitted.

Definition M := Φ A F.

Lemma M_fixpoint : app F M ≅ M.
Proof.
apply Φ_fixpoint.
+ apply F_defined.
+ apply F_growing.
Qed.

Let h_def x y := (x ∈ M /\ tuple x y ∈ f) \/ (~ x ∈ M /\ tuple x y ∈ g).

Definition h := collection A
  (fun x => tuple x (union (comprehension B (h_def x)))).

Lemma function_h : function_def A B h.
Proof.
split.
+ intros u Hu; unfold h.
  exists (union (comprehension B (h_def u))); split.
  - admit.
Admitted.

End CantorBernstein.

