Require Import Morphisms Base BaseProps Cartesian Equipotence.

Record universe (U : V) : Prop := {
  universe_empty : empty ∈ U;
  universe_union : forall x, x ∈ U -> union x ∈ U;
  universe_powerset : forall x, x ∈ U -> powerset x ∈ U
}.

Record small U x : Prop := {
  small_wtn : V;
  small_fun : V;
  small_mem : small_wtn ∈ U;
  small_inj : injection_def x small_wtn small_fun
}.

Instance Proper_small : Proper (V_eq ==> V_eq ==> iff) small.
Proof.
apply proper_sym_impl_iff_2; try apply V_eq_sym.
intros x1 x2 Hx y1 y2 Hy [u f Hu Hf]; exists u f.
+ rewrite <- Hx; assumption.
+ rewrite <- Hy; assumption.
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

Definition bang U A := comprehension (powerset A)
  (fun s => (union s ∈ A) /\ (forall a, a ∈ s -> small U a)).

Lemma coherent_bang : forall U A, coherent_def A -> coherent_def (bang U A).
Proof.
intros U A [Hl Hr]; split.
+ intros x Hx; apply comprehension_spec.
  { repeat intro; repeat f_equiv; try assumption. admit. }
  split; [|split].
  - apply powerset_spec; apply included_spec; intros z Hz; apply union_spec in Hz.
    destruct Hz as [u [Hz Hu]].
  split