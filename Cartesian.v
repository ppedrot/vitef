Require Import Base Morphisms.

Definition tuple (x y : V) : V := pair (singleton x) (pair x y).

Instance Proper_tuple : Proper (V_eq ==> V_eq ==> V_eq) tuple.
Proof.
unfold tuple; intros x1 x2 Hx y1 y2 Hy; rewrite Hx, Hy; reflexivity.
Qed.

Lemma pair_singleton_inj_l : forall x y z,
  singleton x ≅ pair y z -> x ≅ y.
Proof.
intros x y z H.
assert (Hx : x ∈ pair y z).
{ rewrite <- H; apply singleton_spec; reflexivity. }
apply pair_spec in Hx; destruct Hx as [Hx|Hx]; [assumption|].
assert (Hz : y ∈ singleton x).
{ rewrite H; apply pair_spec; left; reflexivity. }
apply singleton_spec in Hz; symmetry; assumption.
Qed.

Lemma pair_singleton_inj_r : forall x y z,
  singleton x ≅ pair y z -> x ≅ z.
Proof.
intros x y z H.
assert (Hrw := pair_singleton_inj_l _ _ _ H).
assert (Hz : z ∈ singleton x).
{ rewrite H; apply pair_spec; right; reflexivity. }
apply singleton_spec in Hz; symmetry; assumption.
Qed.

Lemma tuple_inj_l : forall xl xr yl yr, tuple xl yl ≅ tuple xr yr -> xl ≅ xr.
Proof.
intros xl xr yl yr Heq.
assert (Hxl : singleton xl ∈ tuple xl yl).
{ apply pair_spec; left; reflexivity. }
rewrite Heq in Hxl; apply pair_spec in Hxl; destruct Hxl as [Hl|Hr].
+ apply singleton_spec; rewrite <- Hl; apply singleton_spec; reflexivity.
+ apply pair_singleton_inj_l in Hr; assumption.
Qed.

Lemma tuple_inj_r : forall xl xr yl yr, tuple xl yl ≅ tuple xr yr -> yl ≅ yr.
Proof.
intros xl xr yl yr Heq.
assert (Hxl := tuple_inj_l _ _ _ _ Heq).
rewrite <- Hxl in *; clear xr Hxl.
assert (Hyl : pair xl yl ∈ tuple xl yl).
{ apply pair_spec; right; reflexivity. }
rewrite Heq in Hyl; assert (Hm := Hyl).
apply pair_spec in Hyl; destruct Hyl as [Hl|Hr].
+ symmetry in Hl; apply pair_singleton_inj_r in Hl; rewrite Hl in *; clear xl Hl.
  assert (Hy : pair yl yr ∈ tuple yl yl).
  { rewrite Heq; apply pair_spec; right; reflexivity. }
  apply pair_spec in Hy; destruct Hy as [Hy|Hy].
  - symmetry in Hy; apply pair_singleton_inj_r in Hy; assumption.
  - eapply pair_singleton_inj_r; etransitivity; [|symmetry; eexact Hy].
    clear; apply extensionality; apply included_spec; intros z Hz.
    { apply singleton_spec in Hz; rewrite Hz; apply pair_spec; left; reflexivity. }
    { apply singleton_spec; apply pair_spec in Hz; intuition. }
+ assert (Hy : yl ∈ pair xl yl) by (apply pair_spec; right; reflexivity).
  rewrite Hr in Hy; apply pair_spec in Hy; destruct Hy as [Hy|Hy]; [|assumption].
  rewrite Hy in *; clear yl Hy.
  assert (Hy : yr ∈ pair xl yr) by (apply pair_spec; right; reflexivity).
  rewrite <- Hr in Hy; apply pair_spec in Hy; symmetry; intuition.
Qed.

Definition product (x y : V) : V :=
  union (collection x (fun u => collection y (fun v => tuple u v))).

Instance Proper_product : Proper (V_eq ==> V_eq ==> V_eq) product.
Proof.
intros x1 x2 Hx y1 y2 Hy; unfold product; f_equiv.
apply Proper_collection; [assumption|intros z1 z2 Hz].
apply Proper_collection; [assumption|intros t1 t2 Ht].
f_equiv; assumption.
Qed.

Lemma product_spec : forall x y p,
  p ∈ product x y <-> (exists u, exists v, u ∈ x /\ v ∈ y /\ p ≅ tuple u v).
Proof.
intros x y p; split.
+ intros Hp; apply union_spec in Hp; destruct Hp as [z [Hp Hz]].
  apply collection_spec in Hz.
  - destruct Hz as [u [Hu Hz]]; exists u.
    rewrite Hz in Hp; clear z Hz.
    apply collection_spec in Hp.
    { destruct Hp as [v [Hv Hp]]; exists v; now intuition. }
    { clear; intros x y H; rewrite H; reflexivity. }
  - clear; intros p q Heq; f_equiv; intros a b Hrw; f_equiv; assumption.
+ intros [u [v [Hu [Hv Heq]]]]; apply union_spec.
  exists (collection y (fun v => tuple u v)); split.
  - apply collection_spec.
    { intros ? ? Hrw; unfold tuple; rewrite Hrw; reflexivity. }
    { exists v; split; assumption. }
  - apply collection_spec.
    { clear; intros u1 u2 Hu; f_equiv; intros v1 v2 Hv; f_equiv; assumption. }
    { exists u; split; [assumption|reflexivity]. }
Qed.

Record function_def (x y : V) (f : V) := {
  function_def_def : forall u, u ∈ x -> exists v, v ∈ y /\ tuple u v ∈ f;
  function_def_fun : forall u v1 v2, tuple u v1 ∈ f -> tuple u v2 ∈ f -> v1 ≅ v2
}.

Instance Proper_function_def : Proper (V_eq ==> V_eq ==> V_eq ==> iff) function_def.
Proof.
intros x1 x2 Hx y1 y2 Hy z1 z2 Hz.
refine (let P := _ in conj (P x1 x2 Hx y1 y2 Hy z1 z2 Hz) (P x2 x1 _ y2 y1 _ z2 z1 _));
first [symmetry; assumption|clear].
intros x1 x2 Hx y1 y2 Hy z1 z2 Hz [Hl Hr]; split.
+ intros u Hu; rewrite <- Hx in Hu; destruct (Hl u Hu) as [v Hv].
  exists v; rewrite <- Hy, <- Hz; tauto.
+ intros u v1 v2 Hv1 Hv2; apply (Hr u); rewrite ?Hx, ?Hy, ?Hz; assumption.
Qed.

(* Various utility functions *)

Definition function (x y : V) : V :=
  comprehension (powerset (product x y)) (function_def x y).

Definition app (f : V) (x : V) :=
  union (comprehension (union (union f)) (fun b => tuple x b ∈ f)).

Definition domain (f : V) :=
  comprehension (union (union f)) (fun x => singleton x ∈ union f).

Definition codomain (f : V) :=
  comprehension (union (union f)) (fun y => exists x, x ∈ domain f /\ pair x y ∈ union f).

Definition reify (dom : V) (f : V -> V) : V :=
  collection dom (fun x => tuple x (f x)).

Instance Proper_function : Proper (V_eq ==> V_eq ==> V_eq) function.
Proof.
intros x1 x2 Hx y1 y2 Hy; unfold function; rewrite Hx, Hy; reflexivity.
Qed.

Instance Proper_app : Proper (V_eq ==> V_eq ==> V_eq) app.
Proof.
intros x1 x2 Hx y1 y2 Hy; unfold app.
f_equiv; apply Proper_comprehension.
+ repeat f_equiv; assumption.
+ intros z1 z2 Hz; rewrite Hx, Hy, Hz; reflexivity.
Qed.

Instance Proper_domain : Proper (V_eq ==> V_eq) domain.
Proof.
intros x1 x2 Hx; unfold domain; f_equiv.
+ rewrite Hx; reflexivity.
+ intros y1 y2 Hy; rewrite Hx, Hy; tauto.
Qed.

Instance Proper_reify :
  Proper (V_eq ==> respectful V_eq V_eq ==> V_eq) reify.
Proof.
intros x1 x2 Hx f1 f2 Hf.
refine (let P : forall x1 x2 (Hx : x1 ≅ x2) f1 f2 (Hf : respectful V_eq V_eq f1 f2), _ := _ in
  extensionality _ _ (P x1 x2 Hx f1 f2 Hf) (P x2 x1 _ f2 f1 _)).
+ clear; intros x1 x2 Hx f1 f2 Hf; apply included_spec.
  intros z Hz; unfold reify in *.
  eapply Proper_mem; [reflexivity|idtac|eassumption].
  f_equiv; [symmetry; assumption|].
  clear - Hf; intros x1 x2 Hx; symmetry in Hx.
  rewrite (Hf _ _ Hx), Hx; reflexivity.
+ symmetry; assumption.
+ clear - Hf; intros x1 x2 Hx; symmetry in Hx; rewrite <- (Hf _ _ Hx); reflexivity.
Qed.

Lemma function_spec : forall x y f,
  f ∈ function x y <-> (f ⊆ (product x y) /\ function_def x y f).
Proof.
intros x y f; split; intros H.
+ apply comprehension_spec in H.
  - destruct H as [Hd Hf]; split; [apply powerset_spec|]; assumption.
  - apply Proper_function_def; reflexivity.
+ apply comprehension_spec.
  - apply Proper_function_def; reflexivity.
  - split; [|now intuition].
    apply powerset_spec; tauto.
Qed.

Lemma app_spec : forall x y u v f, f ∈ function x y ->
  (tuple u v ∈ f <-> (u ∈ x /\ app f u ≅ v)).
Proof.
intros x y u v f Hf.
apply function_spec in Hf; destruct Hf as [Hd Hf]; split; intros H.
+ assert (Hp : u ∈ x).
  { apply (mem_included_compat (tuple u v)) in Hd; [|assumption].
    apply product_spec in Hd.
    destruct Hd as [a [b [Ha [Hb Heq]]]]; apply tuple_inj_l in Heq.
    rewrite Heq; assumption.
  }
  split; [assumption|clear Hp].
  apply extensionality; apply included_spec; intros z Hz.
  - apply union_spec in Hz; destruct Hz as [r [Hr Hz]].
    assert (Hrw : v ≅ r); [|rewrite Hrw; assumption].
    apply comprehension_spec in Hz; [|intros x1 x2 Hx; rewrite Hx; reflexivity].
    destruct Hz as [He Hz].
    destruct Hf as [_ Hf]; apply (Hf u); try assumption.
  - apply union_spec; exists v; split; [assumption|].
    apply comprehension_spec; [intros x1 x2 Hx; rewrite Hx; reflexivity|].
    split; [|assumption].
    apply union_spec; exists (pair u v).
    split; [apply pair_spec; right; reflexivity|].
    apply union_spec; exists (tuple u v).
    split; [apply pair_spec; right; reflexivity|].
    assumption.
+ destruct H as [Hu Heq]; rewrite <- Heq; clear v Heq.
  destruct Hf as [Hf Hi].
  destruct (Hf u Hu) as [v [Hv Himg]].
  assert (Hrw : v ≅ app f u); [|rewrite <- Hrw; assumption].
  apply extensionality; apply included_spec; intros z Hz.
  - apply union_spec; exists v; split; [assumption|].
    apply comprehension_spec; [intros x1 x2 Hx; rewrite Hx; reflexivity|].
    split; [|assumption].
    apply union_spec; exists (pair u v).
    split; [apply pair_spec; right; reflexivity|].
    apply union_spec; exists (tuple u v).
    split; [apply pair_spec; right; reflexivity|].
    assumption.
  - apply union_spec in Hz; destruct Hz as [r [Hr Hz]].
    assert (Hrw : r ≅ v); [|rewrite <- Hrw; assumption].
    apply (Hi u); try assumption.
    apply comprehension_spec in Hz; [|intros x1 x2 Hx; rewrite Hx; reflexivity].
    destruct Hz as [Hz Hm]; assumption.
Qed.

Lemma app_defined : forall x y z f, f ∈ function x y -> z ∈ x -> app f z ∈ y.
Proof.
intros x y z f Hf Hz; unfold app.
apply function_spec in Hf; destruct Hf as [Hf [Hdef Hfun]].
assert (Himg := Hz); apply Hdef in Himg; destruct Himg as [v [Hv Himg]].
let e := match goal with [ |- ?e ∈ y ] => e end in
assert (Hrw : e ≅ v); [|rewrite Hrw; assumption].
apply extensionality; apply included_spec; intros r Hr.
+ apply union_spec in Hr; destruct Hr as [s [Hsl Hsr]].
  apply comprehension_spec in Hsr.
  - destruct Hsr as [Hsu Hzs].
    assert (Hrw := Hfun _ _ _ Himg Hzs); rewrite Hrw; assumption.
  - clear; intros ? ? H; rewrite H; tauto.
+ apply union_spec; exists v; split; [assumption|].
  apply comprehension_spec; [|split].
  - clear; intros ? ? H; rewrite H; tauto.
  - apply union_spec; exists (pair z v); split; [apply pair_spec; right; reflexivity|].
    apply union_spec; exists (tuple z v); split; [|assumption].
    apply pair_spec; right; reflexivity.
  - assumption.
Qed.

Lemma domain_defined : forall x y f, f ∈ function x y -> domain f ≅ x.
Proof.
intros x y f Hf.
apply function_spec in Hf; destruct Hf as [Hf [Hdef Hfun]].
apply extensionality; apply included_spec; intros z Hz.
+ apply comprehension_spec in Hz.
  - destruct Hz as [Hzl Hzr].
    apply union_spec in Hzl; destruct Hzl as [u [Hul Hur]].
    apply union_spec in Hzr; destruct Hzr as [v [Hvl Hvr]].
    assert (Hm : v ∈ product x y).
    { apply -> included_spec; eassumption. }
    apply product_spec in Hm; destruct Hm as [a [b [Ha [Hb Hm]]]].
    rewrite Hm in *; clear v Hm.
    assert (Hrw : z ≅ a); [|rewrite Hrw; assumption].
    apply pair_spec in Hvl; destruct Hvl as [Hvl|Hvl].
    { apply singleton_spec; rewrite <- Hvl; apply singleton_spec; reflexivity. }
    { apply pair_singleton_inj_l in Hvl; assumption. }
  - apply proper_sym_impl_iff; [now apply V_eq_sym|].
    clear; intros x1 x2 Hx H; rewrite <- Hx; assumption.
+ apply comprehension_spec; [|split].
  - apply proper_sym_impl_iff; [now apply V_eq_sym|].
    clear; intros x1 x2 Hx H; rewrite <- Hx; assumption.
  - specialize (Hdef z Hz); destruct Hdef as [v [Hvl Hvr]].
    apply union_spec; exists (singleton z).
    split; [apply singleton_spec; reflexivity|].
    apply union_spec; exists (tuple z v); split; [|assumption].
    apply pair_spec; left; reflexivity.
  - specialize (Hdef z Hz); destruct Hdef as [v [Hvl Hvr]].
    apply union_spec; exists (tuple z v); split; [|assumption].
    apply pair_spec; left; reflexivity.
Qed.

Lemma codomain_defined : forall x y f, f ∈ function x y -> codomain f ⊆ y.
Proof.
intros x y f Hf; assert (HF := Hf).
apply function_spec in Hf; destruct Hf as [Hf [Hdef Hfun]].
apply included_spec; intros z Hz.
apply comprehension_spec in Hz.
+ destruct Hz as [Hz [r [Hrl Hrr]]].
  rewrite domain_defined in Hrl; [|eassumption].
  admit.
+ apply proper_sym_impl_iff; [apply V_eq_sym|].
  clear; intros x1 x2 Hx [r Hr]; exists r.
  rewrite <- Hx; assumption.
Qed.

Lemma reify_spec : forall x d f, Proper (V_eq ==> V_eq) f ->
  x ∈ d -> app (reify d f) x ≅ f x.
Proof.
intros x d f Hf Hx.
assert (Hex : extensional (fun x => tuple x (f x))).
{ clear - Hf; intros x1 x2 Hx; rewrite Hx; reflexivity. }
apply extensionality; apply included_spec; intros z Hz.
+ apply union_spec in Hz; destruct Hz as [r [Hz Hr]].
  apply comprehension_spec in Hr.
  - destruct Hr as [Hrl Hrr]; apply union_spec in Hrl.
    destruct Hrl as [s [Hs Hr]]; apply union_spec in Hr.
    destruct Hr as [t [Ht Hr]].
    apply collection_spec in Hr; [|assumption].
    apply collection_spec in Hrr; [|assumption].
    destruct Hr as [a [Ha Har]]; rewrite Har in *; clear t Har.
    destruct Hrr as [b [Hbl Hbr]].
    assert (Hxb := tuple_inj_l _ _ _ _ Hbr); rewrite <- Hxb in *; clear b Hxb.
    assert (Hrb := tuple_inj_r _ _ _ _ Hbr); rewrite Hrb in *; clear r Hrb Hbr.
    assumption.
  - clear; intros x1 x2 Hx; rewrite Hx; tauto.
+ apply union_spec; exists (f x); split; [assumption|].
  apply comprehension_spec; [|split].
  - clear - Hf; intros x1 x2 Hx; rewrite Hx; tauto.
  - apply union_spec; exists (pair x (f x)).
    split; [apply pair_spec; right; reflexivity|].
    apply union_spec; exists (tuple x (f x)); split; [apply pair_spec; right; reflexivity|].
    apply collection_spec; [assumption|].
    exists x; split; [assumption|reflexivity].
  - apply collection_spec; [assumption|].
    exists x; split; [assumption|reflexivity].
Qed.

Lemma reify_defined : forall d f, Proper (V_eq ==> V_eq) f ->
  reify d f ∈ function d (collection d f).
Proof.
intros d f Hf; apply function_spec.
assert (Hex : extensional (fun x => tuple x (f x))).
{ intros x1 x2 Hx; rewrite Hx; reflexivity. }
split; [|split].
+ apply included_spec; intros z Hz; apply product_spec.
  apply collection_spec in Hz; [|assumption].
  - destruct Hz as [u [Hul Hur]].
    exists u, (f u); split; [assumption|].
    split; [|assumption].
    apply collection_spec; [now apply Hf|].
    exists u; split; [assumption|reflexivity].
+ intros u Hu; exists (f u); split.
  - apply collection_spec; [assumption|].
    exists u; split; [assumption|reflexivity].
  - apply collection_spec; [assumption|].
    exists u; split; [assumption|reflexivity].
+ intros u v1 v2 Hv1 Hv2.
  apply collection_spec in Hv1; [|assumption]; destruct Hv1 as [x1 [Hx1 Hf1]].
  apply collection_spec in Hv2; [|assumption]; destruct Hv2 as [x2 [Hx2 Hf2]].
  assert (Hrw := tuple_inj_l _ _ _ _ Hf1); rewrite <- Hrw in *; clear x1 Hrw.
  assert (Hrw := tuple_inj_l _ _ _ _ Hf2); rewrite <- Hrw in *; clear x2 Hrw.
  assert (Hrw := tuple_inj_r _ _ _ _ Hf1); rewrite Hrw in *; clear v1 Hrw.
  assert (Hrw := tuple_inj_r _ _ _ _ Hf2); rewrite Hrw in *; clear v2 Hrw.
  reflexivity.
Qed.

Lemma codomain_included_compat : forall x y z f,
  f ∈ function x y -> y ⊆ z -> f ∈ function x z.
Proof.
intros x y z f Hf Hs.
apply function_spec in Hf; destruct Hf as [Hfl Hfr].
apply function_spec; split.
+ apply included_spec; intros p Hp; apply product_spec.
  assert (Hm : p ∈ product x y).
  { eapply mem_included_compat; eassumption. }
  apply product_spec in Hm; destruct Hm as [u [v [Hu [Hv Heq]]]].
  exists u, v; split; [assumption|]; split; [|assumption].
  eapply mem_included_compat; eassumption.
+ destruct Hfr as [Hfd Hfi]; split.
  - intros u Hu; destruct (Hfd u Hu) as [v [Hv Hf]].
    exists v; split; [|assumption].
    eapply mem_included_compat; eassumption.
  - intros u v1 v2 Hv1 Hv2; eapply Hfi; eassumption.
Qed.

Definition composition (f g : V) : V := reify (domain g) (fun x => app f (app g x)).

Definition id (x : V) := reify x (fun x => x).

Lemma id_spec : forall x y, y ∈ x -> app (id x) y ≅ y.
Proof.
intros x y Hm; unfold id.
rewrite reify_spec; [reflexivity|idtac|assumption].
clear; intros x1 x2 Hx; assumption.
Qed.

Lemma id_function : forall x, id x ∈ function x x.
Proof.
intros x; unfold id.
assert (Hrw : x ≅ collection x (fun x => x)).
{
  apply extensionality; apply included_spec; intros z Hz.
  + apply collection_spec; [repeat intro; assumption|].
    exists z; split; [assumption|reflexivity].
  + apply collection_spec in Hz; [|repeat intro; assumption].
    destruct Hz as [e [Hz1 Hz2]]; rewrite Hz2; assumption.
}
rewrite Hrw at 3; apply reify_defined.
clear; intros x1 x2 Hx; assumption.
Qed.

(* Lemma functional_extensionality : forall s t f g,
  f ∈ function s t -> g ∈ function s t ->
  (forall x, app f x ≅ app g x) -> f ≅ g.
Proof.
intros f g Heq; apply extensionality; apply included_spec.
+ intros z Hz. *)
