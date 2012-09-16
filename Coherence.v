Require Import Morphisms Base Cartesian Equipotence.

Require Import Ordinal.

Definition U0 := union (compre

Record small U x : Prop := {
  small_wtn : V;
  small_fun : V;
  small_mem : small_wtn ∈ U;
  small_inj : injection_def x small_wtn small_fun
}.

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



Definition cap x y := comprehension x (fun z => z ∈ y).

Instance Proper_cap : Proper (V_eq ==> V_eq ==> V_eq) cap.
Proof.
intros x1 x2 Hx y1 y2 Hy; unfold cap; f_equiv; [assumption|].
intros z1 z2 Hz; rewrite Hy, Hz; reflexivity.
Qed.

Lemma cap_spec : forall x y z, z ∈ cap x y <-> (z ∈ x /\ z ∈ y).
Proof.
intros x y z; split; intros H.
+ apply comprehension_spec in H; [|intros x1 x2 Hx; rewrite Hx; reflexivity].
  assumption.
+ apply comprehension_spec; [|assumption].
  intros x1 x2 Hx; rewrite Hx; reflexivity.
Qed.

Definition orthogonal x y := forall z1 z2, z1 ∈ cap x y -> z2 ∈ cap x y -> z1 ≅ z2.

Definition web A := union A.

Record coherent_def A : Prop := {
  coherent_def_bin : forall x,
    (forall x1 x2, x1 ∈ x -> x2 ∈ x -> cup x1 x2 ∈ A) -> union x ∈ A;
  coherent_def_stb : forall x1 x2, x1 ∈ A -> x2 ∈ A -> cup x1 x2 ∈ A -> cap x1 x2 ∈ A
}.

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
+ intros x1 x2 Hx1 Hx2 Hx; apply singleton_spec.
  apply singleton_spec in Hx1; apply singleton_spec in Hx2; rewrite Hx1, Hx2.
  apply extensionality; apply included_spec; intros z Hz.
  - apply cap_spec in Hz; destruct Hz as [Hz _]; apply empty_spec in Hz; contradiction.
  - apply empty_spec in Hz; contradiction.
Qed.

Record Small U x := {
  Small_elt : V;
  Small_spc : Small_elt ∈ U;
  Small_def : forall α, α ∈ x -> exists β, β ∈ Small_elt /\ 
}.

Definition bang U A := comprehension (powerset A) (Small u).
