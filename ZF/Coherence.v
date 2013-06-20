Require Import Morphisms Base BaseProps Cartesian Equipotence Ordinal.

Record small U x : Prop := {
  small_wtn : V;
  small_fun : V;
  small_mem : small_wtn ∈ U;
  small_inj : injection_def x small_wtn small_fun
}.

Lemma small_included_compat : forall U x y, small U x -> y ⊆ x -> small U y.
Proof.
intros U x y [w f Hw Hf] Hm.
pose (fr := comprehension f (fun p => exists u, exists v, p ≅ tuple u v /\ u ∈ y)).
assert (Hfr : forall u v, tuple u v ∈ fr <-> (tuple u v ∈ f /\ u ∈ y)).
{ intros u v; split; intros H.
  + apply comprehension_spec in H; [|repeat intro; repeat (f_equiv; intro); repeat f_equiv; assumption].
    destruct H as [? [? [? [Heq ?]]]].
    split; [assumption|apply tuple_inj_l in Heq; rewrite Heq; intuition].
  + apply comprehension_spec; [repeat intro; repeat (f_equiv; intro); repeat f_equiv; assumption|].
    split; [now intuition|].
    exists u, v; split; intuition.
}
exists w fr; [assumption|]; destruct Hf as [Hf1 Hf2 Hf3]; split.
+ intros u Hu.
  destruct (Hf1 u) as [v [Hv Hp]]; [eapply mem_included_compat; eassumption|].
  exists v; split; [assumption|].
  apply Hfr; now intuition.
+ intros u v1 v2 Hv1 Hv2; apply Hfr in Hv1; apply Hfr in Hv2.
  eapply Hf2; intuition eauto.
+ intros u1 u2 v Hu1 Hu2; apply Hfr in Hu1; apply Hfr in Hu2.
  eapply Hf3; intuition eauto.
Qed.

(* Lemma toto : forall x, small omega x ->
  (forall y, y ∈ x -> small omega y) -> small omega (union x).
Proof.
intros x [n f Hn Hf] Hm.
apply omega_spec in Hn; destruct Hn as [N Hn].
assert (Hdf : forall α, α ∈ x -> exists p, app f α ≅ ordinal_of_nat p).
{ intros α Hα; destruct Hf as [Hf1 Hf2 Hf3].
  destruct (Hf1 _ Hα) as [p [Hp Hf]]; rewrite Hn in Hp.
  assert (HP : exists P, p ≅ ordinal_of_nat P).
  { clear - Hp; revert p Hp; induction N; intros p Hp.
    + apply empty_spec in Hp; contradiction.
    + simpl in Hp; apply cup_spec in Hp; destruct Hp as [Hp|Hp].
      - apply IHN; assumption.
      - apply singleton_spec in Hp; exists N; assumption. }
  destruct HP as [P HP]; exists P; rewrite <- HP.
  admit. }



assert (Hf : exists g, forall α, α ∈ x -> g α).
pose (size := fun x => union (comprehension omega (fun m => tuple x m ∈ f))).
pose (M := union (collection x size)).
assert (Hsize : forall α, α ∈ x -> size α ∈ omega).
{ intros α Hα; destruct (Hm _ Hα) as [p F Hp HF].
  apply omega_spec exists p.


revert x n f Hn Hf Hm; induction N; intros x n f Hn Hf Hm.
+ simpl ordinal_of_nat in Hn.
  assert (Hrw : x ≅ empty).
  { apply extensionality; apply included_spec; intros z Hz.
    - destruct Hf as [Hf _ _]; specialize (Hf _ Hz).
      destruct Hf as [e [He _]]; rewrite Hn in He.
      apply empty_spec in He; contradiction.
    - apply empty_spec in Hz; contradiction. }
  admit.
+ simpl ordinal_of_nat in Hn; unfold successor in Hn.
  assert (Hrw : exists y z, x ≅ cup (singleton y) z). *)

Definition orthogonal x y := forall z1 z2, z1 ∈ cap x y -> z2 ∈ cap x y -> z1 ≅ z2.

Definition web A := union A.

Record coherent_def A : Prop := {
  coherent_def_bin : forall x,
    (forall x1 x2, x1 ∈ x -> x2 ∈ x -> cup x1 x2 ∈ A) -> union x ∈ A;
  coherent_def_stb : forall x1 x2, x1 ∈ A -> x2 ⊆ x1 -> x2 ∈ A
}.

Definition coherent_def_alt (A : V) (R : V -> V -> Prop) : Prop := forall x, x ∈ A -> R x x.

Definition to_alt A := (union A, fun x y => pair x y ∈ A).

Definition of_alt A (R : V -> V -> Prop) :=
  comprehension (powerset A) (fun a => forall x y, x ∈ a -> y ∈ a -> R x y).

Lemma of_alt_sound : forall A R, Proper (V_eq ==> V_eq ==> iff) R ->
  coherent_def_alt A R -> coherent_def (of_alt A R).
Proof.
assert (HP : forall (R : V -> V -> Prop),
  Proper (V_eq ==> iff) (fun a => forall x y, x ∈ a -> y ∈ a -> R x y)).
{ intros R; apply proper_sym_impl_iff; [apply V_eq_sym|].
  intros x1 x2 Hx H x y; rewrite <- Hx; intuition. }
intros A R HR Hc; split.
+ intros x Hx; apply comprehension_spec; [now auto|split].
  - apply powerset_spec; apply included_spec; intros z Hz.
    apply union_spec in Hz; destruct Hz as [u [Hz Hu]].
    specialize (Hx _ _ Hu Hu); rewrite cup_idem in Hx.
    apply comprehension_spec in Hx; [|now auto].
    eapply mem_included_compat; [eassumption|]; apply powerset_spec; intuition.
  - intros u1 u2 Hu1 Hu2.
    apply union_spec in Hu1; destruct Hu1 as [z1 [Hu1 Hz1]].
    apply union_spec in Hu2; destruct Hu2 as [z2 [Hu2 Hz2]].
    specialize (Hx z1 z2 Hz1 Hz2); apply comprehension_spec in Hx; [|now auto].
    apply Hx; apply cup_spec; intuition.
+ intros x1 x2 Hx1 Hm.
  apply comprehension_spec in Hx1; [|now auto].
  apply comprehension_spec; [now auto|]; split.
  - apply powerset_spec; transitivity x1; [eassumption|]; apply powerset_spec; intuition.
  - intros x y Hx Hy; apply Hx1; eapply mem_included_compat; eassumption.
Qed.

Lemma to_alt_sound : forall A,
  coherent_def A -> coherent_def_alt (fst (to_alt A)) (snd (to_alt A)).
Proof.
intros A HA; unfold to_alt; simpl; intros x Hx.
apply union_spec in Hx; destruct Hx as [z [Hx Hz]].
destruct HA as [HAl HAr]; apply (HAr (union (singleton z))).
+ apply HAl; intros z1 z2 Hz1 Hz2; apply singleton_spec in Hz1; apply singleton_spec in Hz2.
  rewrite Hz1, Hz2, cup_idem; assumption.
+ apply included_spec; intros u Hu; apply pair_spec in Hu.
  assert (Hrw : u ≅ x) by intuition; rewrite Hrw in *; clear u Hu Hrw.
  apply union_spec; exists z; split; [assumption|apply singleton_spec; reflexivity].
Qed.

Definition coh_le A B :=
  union A ⊆ union B /\ (forall a, a ⊆ union A -> (a ∈ A <-> a ∈ B)).

Lemma coh_le_included_compat : forall A B, coh_le A B -> A ⊆ B.
Proof.
intros A B [Hl Hr]; apply included_spec; intros a Ha.
apply Hr; [|assumption].
apply included_spec; intros α Hα; apply union_spec.
exists a; intuition.
Qed.

Definition coh_nul := singleton empty.

Lemma coherent_nul : coherent_def coh_nul.
Proof.
split.
+ intros x Hs; apply singleton_spec.
  assert (He : forall z, z ∈ x -> z ≅ empty).
  { intros z Hz; specialize (Hs _ _  Hz Hz).
    apply singleton_spec in Hs; rewrite <- Hs.
    clear; apply extensionality; apply included_spec; intros u Hu.
    - apply cup_spec; intuition.
    - apply cup_spec in Hu; intuition.
  }
  apply extensionality; apply included_spec.
  - intros z Hz; apply union_spec in Hz; exfalso.
    destruct Hz as [m [Hz Hm]].
    rewrite (He _ Hm) in Hz; apply empty_spec in Hz; contradiction.
  - intros z Hz; apply empty_spec in Hz; contradiction.
+ intros x1 x2 Hx1 Hm; apply singleton_spec.
  apply singleton_spec in Hx1; rewrite Hx1 in Hm; clear x1 Hx1.
  apply extensionality; apply included_spec; intros z Hz.
  - apply (mem_included_compat _ _ _ Hz) in Hm; assumption.
  - apply empty_spec in Hz; contradiction.
Qed.

Definition coh_bang U A := comprehension (powerset A)
  (fun a => (forall x, x ∈ a -> (small U x)) /\ union a ∈ A).

Lemma coherent_bang : forall U A, coherent_def A -> coherent_def (coh_bang U A).
Proof.
assert (HP : forall U A,
  Proper (V_eq ==> iff) (fun a => (forall x, x ∈ a -> (small U x)) /\ union a ∈ A)).
{ intros U A x1 x2 Hx; repeat f_equiv; [|assumption].
  split; intros H x; [rewrite <- Hx|rewrite Hx]; intuition. }
intros U A [Hl Hr]; split.
+ intros a Ha; apply comprehension_spec; [now auto|].
  split; [|split].
  - apply powerset_spec; apply included_spec; intros z Hz.
    apply union_spec in Hz; destruct Hz as [u [Hz Hu]].
    specialize (Ha _ _ Hu Hu); rewrite cup_idem in Ha.
    apply comprehension_spec in Ha; [|now auto].
    destruct Ha as [Ha _]; apply powerset_spec in Ha.
    eapply mem_included_compat; eassumption.
  - intros u Hu; apply union_spec in Hu; destruct Hu as [x [Hu Hx]].
    specialize (Ha _ _ Hx Hx); rewrite cup_idem in Ha.
    apply comprehension_spec in Ha; [|now auto].
    destruct Ha as [_ [Ha _]]; apply Ha; assumption.
  - apply Hl; intros x1 x2 Hx1 Hx2.
    apply union_spec in Hx1; apply union_spec in Hx2.
    destruct Hx1 as [z1 [Hx1 Hz1]]; destruct Hx2 as [z2 [Hx2 Hz2]].
    specialize (Ha _ _ Hz1 Hz2).
    apply comprehension_spec in Ha; [|auto].
    destruct Ha as [_ [_ Ha]].
    apply (coherent_def_stb A (Build_coherent_def _ Hl Hr) _ _ Ha).
    apply included_spec; intros p Hp; apply cup_spec in Hp.
    apply union_spec.
    destruct Hp as [Hp|Hp].
    { exists x1; split; [assumption|]; apply cup_spec; intuition. }
    { exists x2; split; [assumption|]; apply cup_spec; intuition. }
+ intros x1 x2 Hx1 Hm; apply comprehension_spec; [now auto|].
  apply comprehension_spec in Hx1; [|now auto].
  split; [|split].
  - apply powerset_spec; apply included_spec; intros z Hz.
    eapply mem_included_compat; [eassumption|].
    transitivity x1; [assumption|].
    apply powerset_spec; intuition.
  - intros z Hz; apply Hx1.
    eapply mem_included_compat; eassumption.
  - apply Hl; intros y1 y2 Hy1 Hy2.
    apply (Hr (union x1)); [now intuition|].
    apply included_spec; intros z Hz; apply cup_spec in Hz.
    apply union_spec; destruct Hz as [Hz|Hz]; [exists y1|exists y2]; intuition;
    eapply mem_included_compat; eassumption.
Qed.

Lemma coh_bang_spec : forall U A a,
  a ∈ coh_bang U A <-> (a ⊆ A /\ union a ∈ A /\ (forall x, x ∈ a -> small U x)).
Proof.
assert (HP : forall U A,
  Proper (V_eq ==> iff) (fun a => (forall x, x ∈ a -> (small U x)) /\ union a ∈ A)).
{ intros U A x1 x2 Hx; repeat f_equiv; [|assumption].
  split; intros H x; [rewrite <- Hx|rewrite Hx]; intuition. }
intros U A a; split; intros H.
+ apply comprehension_spec in H; [|now auto]; split; [|split]; try solve [intuition].
  apply powerset_spec; intuition.
+ apply comprehension_spec; [now auto|]; split; [|split]; try solve [intuition].
  apply powerset_spec; intuition.
Qed.

Lemma coh_bang_monotonous : forall U A B, coh_le A B -> coh_le (coh_bang U A) (coh_bang U B).
Proof.
intros U A B [Hl Hr]; split.
+ apply included_spec; intros a Ha; apply union_spec in Ha.
  destruct Ha as [u [Ha Hu]]; apply union_spec; exists u; split; [assumption|].
  apply coh_bang_spec in Hu; apply coh_bang_spec.
  split; [|split]; [| |now intuition].
  - transitivity A; [|apply coh_le_included_compat; constructor]; intuition.
  - eapply mem_included_compat; [intuition eauto|].
    apply coh_le_included_compat; constructor; intuition.
+ intros a Ha.
Admitted.

Lemma coh_bang_monotonous : forall U A B, A ⊆ B -> coh_bang U A ⊆ coh_bang U B.
Proof.
assert (HP : forall U A,
  Proper (V_eq ==> iff) (fun a => (forall x, x ∈ a -> (small U x)) /\ union a ∈ A)).
{ intros U A x1 x2 Hx; repeat f_equiv; [|assumption].
  split; intros H x; [rewrite <- Hx|rewrite Hx]; intuition. }
intros U A B Hs; apply included_spec; intros a Ha.
apply comprehension_spec in Ha; [|now auto].
apply comprehension_spec; [now auto|]; split; [|split].
+ apply powerset_spec; transitivity A; [|assumption].
  apply powerset_spec; intuition.
+ intuition.
+ eapply mem_included_compat; intuition eauto.
Qed.

Definition injl x := tuple (ordinal_of_nat 0) x.
Definition injr y := tuple (ordinal_of_nat 1) y.
Definition sum x y := cup (collection x injl) (collection y injr).

Definition coh_rel A B s1 s2 :=
  (exists x1 x2, s1 ≅ injl x1 /\ s2 ≅ injl x2 /\ x1 ∈ A /\ x2 ∈ A) \/
  (exists y1 y2, s1 ≅ injr y1 /\ s2 ≅ injr y2 /\ y1 ∈ B /\ y2 ∈ B).

Definition coh_sum A B := of_alt (sum (union A) (union B)) (coh_rel (union A) (union B)).

Lemma coherent_sum : forall A B, coherent_def A -> coherent_def B -> coherent_def (coh_sum A B).
Proof.
assert (HP : forall A B, Proper (V_eq ==> V_eq ==> iff) (coh_rel A B)).
{ unfold coh_rel, injl, injr.
  intros A B x1 x2 Hx y1 y2 Hy; repeat f_equiv; intro u; f_equiv; intro v; f_equiv;
  repeat f_equiv; assumption. }
intros A B HA HB; apply of_alt_sound; [now auto|].
intros x Hx; apply cup_spec in Hx; destruct Hx as [Hx|Hx].
+ apply collection_spec in Hx; [|unfold injl; repeat intro; f_equiv; assumption].
  destruct Hx as [z [Hx Hz]]; left; exists z, z; intuition.
+ apply collection_spec in Hx; [|unfold injr; repeat intro; f_equiv; assumption].
  destruct Hx as [z [Hx Hz]]; right; exists z, z; intuition.
Qed.

Lemma coh_sum_monotonous : forall A B C D, A ⊆ B -> C ⊆ D -> coh_sum A C ⊆ coh_sum B D.
Proof.
assert (HP : forall A B, Proper (V_eq ==> V_eq ==> iff) (coh_rel A B)).
{ unfold coh_rel, injl, injr.
  intros A B x1 x2 Hx y1 y2 Hy; repeat f_equiv; intro u; f_equiv; intro v; f_equiv;
  repeat f_equiv; assumption. }
intros A B C D Hl Hr; apply included_spec; intros z Hz.
apply comprehension_spec; [|].
Admitted.

Definition small_basetype U X :=
  (forall x, x ∈ X -> small U x) /\ (forall x a, x ∈ X -> a ∈ x -> small U a).
Definition basetype_def U A X :=
  (forall x1 x2, x1 ∈ X -> x2 ∈ X -> cup x1 x2 ∈ A -> x1 ≅ x2) /\ small_basetype U X.
Definition basetype U A := comprehension (powerset A) (basetype_def U A).

Definition coh_flat A := of_alt A (fun x y => x ≅ y).

Lemma coherent_flat : forall A, coherent_def (coh_flat A).
Proof.
assert (HP : Proper (V_eq ==> iff) (fun a : V => forall x y : V, x ∈ a -> y ∈ a -> x ≅ y)).
{ apply proper_sym_impl_iff; [apply V_eq_sym|]; intros z1 z2 Hz H u v; rewrite <- Hz; auto. }
intros A; split.
+ intros x Hx; apply comprehension_spec; [assumption|split].
  - apply powerset_spec, included_spec; intros z Hz.
    apply union_spec in Hz; destruct Hz as [y [Hz Hy]].
    specialize (Hx _ _ Hy Hy); rewrite cup_idem in Hx.
    apply comprehension_spec in Hx; [|assumption].
    eapply mem_included_compat; [eassumption|].
    apply powerset_spec; intuition.
  - intros u v Hu Hv.
    apply union_spec in Hu; destruct Hu as [a [Hu Ha]].
    apply union_spec in Hv; destruct Hv as [b [Hv Hb]].
    specialize (Hx _ _ Ha Hb).
    apply comprehension_spec in Hx; [|assumption].
    apply Hx; apply cup_spec; intuition.
+ intros x1 x2 Hx1 Hm.
  apply comprehension_spec in Hx1; [|assumption].
  apply comprehension_spec; [assumption|split].
  - apply powerset_spec; transitivity x1; [assumption|].
    apply powerset_spec; intuition.
  - intros x y Hx Hy; apply Hx1;
    eapply mem_included_compat; eassumption.
Qed.

Definition coh_type U A := coh_flat (basetype U A).

Lemma coherent_type : forall U A, coherent_def (coh_type U A).
Proof.
intros U A; apply coherent_flat.
Qed.



Axiom Hierarchy : nat -> V.
Axiom Top : V.
Axiom Hierarchy_mem : forall n, Hierarchy n ∈ Hierarchy (S n).
Axiom Top_mem : forall n, Hierarchy n ∈ Top.
Axiom Hierarchy_universe : forall n, universe (Hierarchy n).

