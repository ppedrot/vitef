Require Import Morphisms Relations Wellfounded Base BaseProps.

Definition transitive_set (x : V) := forall z, z ∈ x -> z ⊆ x.

Definition transitive_set_alt : forall x y z, transitive_set x -> z ∈ y -> y ∈ x -> z ∈ x.
Proof.
intros x y z Ht Hl Hr.
apply (mem_included_compat _ y); auto.
Qed.

Record ordinal (x : V) : Prop := {
  ordinal_trans : transitive_set x;
  ordinal_trans_trans : forall z, z ∈ x -> transitive_set z
}.

Lemma ordinal_mem_compat : forall x y, ordinal x -> y ∈ x -> ordinal y.
Proof.
intros x y [Hxl Hxr] Hm; split.
+ apply Hxr; assumption.
+ intros z Hz; apply Hxr; eapply transitive_set_alt; eassumption.
Qed.

Lemma ordinal_empty : ordinal empty.
Proof.
split.
+ intros z Hz; exfalso; eapply empty_spec; eassumption.
+ intros z Hz; exfalso; eapply empty_spec; eassumption.
Qed.

Lemma ordinal_max : forall x, (forall y, y ∈ x -> ordinal y) -> ordinal (union x).
Proof.
intros x Hx; split.
+ intros z Hz; apply included_spec; intros u Hu.
  apply union_spec in Hz; destruct Hz as [v [Hv Hz]].
  assert (Hzo := Hx _ Hz); destruct Hzo as [Hzo _].
  specialize (Hzo _ Hv).
  apply union_spec; exists v; split; [|assumption].
  eapply mem_included_compat; eassumption.
+ intros z Hz u Hu.
  apply union_spec in Hz; destruct Hz as [w [Hz Hw]].
  apply Hx in Hw; destruct Hw as [Hwl Hwr].
  apply Hwr; eassumption.
Qed.

Lemma ordinal_union : forall x, ordinal x -> ordinal (union x).
Proof.
intros x Hx; apply ordinal_max.
intros; eapply ordinal_mem_compat; eassumption.
Qed.

Definition successor (x : V) := cup x (singleton x).

Lemma ordinal_successor : forall x, ordinal x -> ordinal (successor x).
Proof.
intros x [Hxl Hxr]; split.
+ intros y Hy; apply -> cup_spec in Hy; destruct Hy as [?|Hy].
  - intros z Hz; apply <- cup_spec.
    left; apply (Hxl y); assumption.
  - intros z Hz; apply <- cup_spec.
    apply -> singleton_spec in Hy.
    left; rewrite <- Hy; apply subrelation_mem_rel; assumption.
+ intros y Hy; apply -> cup_spec in Hy; destruct Hy as [?|Hy].
  - now auto.
  - apply -> singleton_spec in Hy; intros z Hz.
    rewrite Hy; apply Hxl; rewrite <- Hy; assumption.
Qed.

Lemma wf_irrefl : forall A R (x : A), well_founded R -> ~ R x x.
Proof.
intros A R x H; specialize (H x); induction H as [x H IH]; intros Hc.
eapply IH; eassumption.
Qed.

Lemma successor_inj : forall x y, successor x ≅ successor y -> x ≅ y.
Proof.
intros x; intros y Heq.
unfold successor in Heq.
assert (Hx : x ∈ cup y (singleton y)).
{ rewrite <- Heq; apply cup_spec; right; apply singleton_spec; reflexivity. }
assert (Hy : y ∈ cup x (singleton x)).
{ rewrite Heq; apply cup_spec; right; apply singleton_spec; reflexivity. }
apply cup_spec in Hx; apply cup_spec in Hy.
destruct Hx as [Hx|Hx]; [|apply singleton_spec in Hx; assumption].
destruct Hy as [Hy|Hy]; [|apply singleton_spec in Hy; symmetry; assumption].
assert (HR : clos_trans _ mem x x).
{ eright; [left|left]; eassumption. }
exfalso; eapply (wf_irrefl _ _ x); [|eexact HR].
apply wf_clos_trans; apply wf_mem.
Qed.

Fixpoint ordinal_of_nat (n : nat) : V :=
match n with
| 0 => empty
| S n => successor (ordinal_of_nat n)
end.

Lemma ordinal_of_nat_inj : forall m n,
  ordinal_of_nat m ≅ ordinal_of_nat n -> m = n.
Proof.
intros m; induction m as [|m]; intros n Heq; simpl in *.
+ destruct n; [reflexivity|exfalso]; simpl in *.
  apply (empty_spec (ordinal_of_nat n)); rewrite Heq.
  apply cup_spec; right; apply singleton_spec; reflexivity.
+ destruct n; [exfalso|]; simpl in *.
  - apply (empty_spec (ordinal_of_nat m)); rewrite <- Heq; simpl.
    apply cup_spec; right; apply singleton_spec; reflexivity.
  - f_equal; apply IHm; apply successor_inj; assumption.
Qed.

Definition omega : V := @V_const nat ordinal_of_nat.

Lemma omega_spec : forall x, x ∈ omega <-> (exists n, x ≅ ordinal_of_nat n).
Proof.
intros x; split; intros H.
+ destruct H as [e Heq He].
  cut (exists n, e ≅ ordinal_of_nat n).
  - intros [n Hn]; exists n; rewrite <- Heq; assumption.
  - clear x Heq; pattern e.
    let P := match goal with [|- ?P e] => P end in
    revert He; eapply (@V_rel_inv _ _ P).
    intros n; exists n; reflexivity.
+ destruct H as [n Hn].
  exists (ordinal_of_nat n); [symmetry; assumption|constructor].
Qed.

Fixpoint Vfix (f : V -> V -> V) (x : V) : V :=
match x with
| V_const X Xf => @V_const X (fun e => f (Xf e) (Vfix f (Xf e)))
end.

Lemma Vfix_spec : forall f x, Vfix f x ≅ collection x (fun y => f y (Vfix f y)).
Proof.
intros f x; destruct x; reflexivity.
Qed.

Instance Proper_Vfix : Proper ((V_eq ==> V_eq ==> V_eq) ==> V_eq ==> V_eq) Vfix.
Proof.
assert (HP : forall X1 Xf1 X2 Xf2 (Hx : @V_const X1 Xf1 ≅ @V_const X2 Xf2)
  f1 f2 (Hf : (V_eq ==> V_eq ==> V_eq)%signature f1 f2)
  (Heq : forall e1 e2, Xf1 e1 ≅ Xf2 e2 -> Vfix f1 (Xf1 e1) ≅ Vfix f2 (Xf2 e2)),
  Vfix f1 (V_const Xf1) ⊆ Vfix f2 (V_const Xf2)).
{
  intros X1 Xf1 X2 Xf2 Hx f1 f2 Hf Heq xs Hxs.
  assert (Hrw : exists α, xs = f1 (Xf1 α) (Vfix f1 (Xf1 α))).
  { clear - Hxs; simpl in Hxs.
    let T := type of Hxs in
    let f := match T with V_rel _ (V_const ?f) => f end in
    set (F := f) in *; change (exists e, xs = F e).
    clearbody F; clear - Hxs; pattern xs.
    eapply (V_rel_inv _ F); [intuition eauto|assumption]. }
  destruct Hrw as [α Hrw]; rewrite Hrw in *; clear xs Hxs Hrw.
  pose (Hα := Hx); destruct Hα as [Hα _].
  specialize (Hα (Xf1 α) (V_rel_def _ _)); destruct Hα as [ys [Hyl Hyr]].
  assert (Hrw : exists β, ys = Xf2 β).
  { clear - Hyl; simpl in Hyl.
    pattern ys; eapply (V_rel_inv _ Xf2); intuition eauto. }
  destruct Hrw as [β Hrw]; rewrite Hrw in *; clear ys Hrw Hyl.
  specialize (Heq _ _ Hyr).
  exists (f2 (Xf2 β) (Vfix f2 (Xf2 β))).
  - symmetry; apply Hf; assumption.
  - simpl.
    let f := match goal with [ |- ?t ε V_const ?f ] => f end in
    change (f β ε V_const f); constructor.
}
intros f1 f2 Hf x1; induction x1 as [X1 X1f IH]; intros [X2 X2f] Hx.
apply extensionality; apply HP; try assumption.
+ intros; apply IH; assumption.
+ symmetry; assumption.
+ symmetry; assumption.
+ intros; symmetry; apply IH; symmetry; assumption.
Qed.


(* Definition collection_dep x (f : forall y, y ∈ x -> V) :=
match x return (forall y, y ∈ x -> V) -> V with
| V_const X Xf => fun f => @V_const X (fun y => f (Xf y) (subrelation_mem_rel _ _ (V_rel_def Xf y)))
end f.

Lemma collection_dep_spec : forall x y f,
  y ∈ collection_dep x f <-> exists z, exists (H : z ∈ x), y ≅ f z H.
Proof.
Admitted.

Lemma transitive_closure : forall x, {y | forall z, z ∈ y <-> clos_trans _ mem z x}.
Proof.
intros x; induction (wf_mem x) as [x _ IH].
pose (R := collection_dep x (fun y Hy => proj1_sig (IH _ Hy))).
exists (cup R x); intros z; split; intros Hz.
+ apply cup_spec in Hz; destruct Hz as [Hz|Hz].
  - apply collection_dep_spec in Hz; destruct Hz as [u [Hm Hu]].
    destruct (IH u Hm) as [v Hv]; simpl in Hu.
    replace z with v; [|admit]; clear z Hu.
    admit.
  - admit.
+ admit.
Defined.

Extraction transitive_closure.

Fixpoint transitive_closure x :=
match x with
| V_const X Xf => 
end.

Definition Vω := F (fun _ y => collection y powerset) omega.

Lemma Vω_empty : empty ∈ Vω.
Proof.
unfold Vω; rewrite F_spec; apply collection_spec; [admit|].
exists (ordinal_of_nat 0); split; [apply omega_spec; exists 0; reflexivity|].
apply extensionality; apply included_spec; intros z Hz.
+ apply empty_spec in Hz; contradiction.
+
  rewrite F_spec in Hz.
exfalso; apply collection_spec in Hz; [|admit].
  destruct Hz as [x [Hz _]].
  apply collection_spec in Hz; [|admit].
  destruct Hz as [? [Hz _]]; apply empty_spec in Hz; contradiction.
Qed.

Lemma Vω_powerset : forall x, x ∈ Vω -> powerset x ∈ Vω.
Proof.
intros x Hx; unfold Vω in *.
rewrite F_spec in Hx; apply collection_spec in Hx; [|admit].
rewrite F_spec; apply collection_spec; [admit|].

Lemma ordinal_rect : forall P,
  (forall x, ordinal x -> (forall y, y ∈ x -> P y) -> P x) -> forall x, ordinal x -> P x.
Proof.
intros P IH x Hx.
induction (wf_mem x) as [x H IHx].
apply IH; [assumption|].
intros y Hy; apply IHx; [assumption|eapply ordinal_mem_compat; eassumption].
Qed.
*)