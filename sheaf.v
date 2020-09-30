Axiom funext : forall A (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.
Axiom pi : forall (A : Prop) (p q : A), p = q.

Set Primitive Projections.

Record cat := {
  cat_obj : Type;
  cat_hom : cat_obj -> cat_obj -> Type;
  cat_id : forall (p : cat_obj), cat_hom p p;
  cat_cmp : forall p q r, cat_hom p q -> cat_hom q r -> cat_hom p r;
  cat_cmp_l : forall p q (α : cat_hom p q), cat_cmp p p q (cat_id p) α = α;
  cat_cmp_r : forall p q (α : cat_hom p q), cat_cmp p q q α (cat_id q) = α;
  cat_cmp_cmp : forall p q r s (α : cat_hom p q) (β : cat_hom q r) (γ : cat_hom r s),
    cat_cmp p r s (cat_cmp p q r α β) γ = cat_cmp p q s α (cat_cmp q r s β γ)
}.

Coercion cat_obj : cat >-> Sortclass.
Coercion cat_hom : cat >-> Funclass.

Arguments cat_id {_}.
Arguments cat_cmp {_ _ _ _}.

Notation "α ∘ β" := (cat_cmp α β) (at level 50).
Notation id := cat_id.

Record psh (ℙ : cat) := {
  psh_obj : ℙ -> Type;
  psh_mon : forall p q (α : ℙ q p), psh_obj p -> psh_obj q;
  psh_mon_id : forall p (x : psh_obj p), psh_mon p p (id p) x = x;
  psh_mon_cmp : forall p q r (α : ℙ q p) (β : ℙ r q) (x : psh_obj p),
    psh_mon _ _ (β ∘ α) x = psh_mon _ _ β (psh_mon _ _ α x);
}.

Coercion psh_obj : psh >-> Funclass.

Arguments psh_mon {_} _ {_ _}.

Notation θ := psh_mon.

Record nat {ℙ : cat} (A B : psh ℙ) (p : ℙ) := {
  nat_fun : forall q (α : ℙ q p), A q -> B q; 
  nat_nat : forall q r (α : ℙ q p) (β : ℙ r q) (x : A q),
    θ B β (nat_fun q α x) = nat_fun r (β ∘ α) (θ A β x)
}.

Arguments nat_fun {_ _ _ _}.
Arguments nat_nat {_ _ _ _}.

Coercion nat_fun : nat >-> Funclass.

Lemma nat_fun_eq : forall ℙ A B p (f g : @nat ℙ A B p),
  f.(nat_fun) = g.(nat_fun) -> f = g.
Proof.
intros ℙ A B p [f Hf] [g Hg] e.
cbn in e; destruct e.
replace Hf with Hg by apply pi.
reflexivity.
Qed.

Lemma eq_nat_fun : forall ℙ A B p (f g : @nat ℙ A B p),
  f = g -> f.(nat_fun) = g.(nat_fun).
Proof.
destruct 1; reflexivity.
Qed.

Definition Arr {ℙ} (A B : psh ℙ) : psh ℙ.
Proof.
unshelve econstructor.
+ refine (fun p => nat A B p).
+ unshelve refine (fun p q α f => Build_nat _ _ _ _ _ _).
  - refine (fun r β x => f.(nat_fun) _ (β ∘ α) x).
  - intros r s β γ x; cbn in *.
    rewrite cat_cmp_cmp.
    apply (f.(nat_nat)).
+ cbn; intros p [f Hf].
  apply nat_fun_eq; cbn.
  apply funext; intros q; apply funext; intros α; apply funext; intros x.
  rewrite cat_cmp_r; reflexivity.
+ intros p q r α β [f Hf]; cbn in *. 
  apply nat_fun_eq; cbn.
  apply funext; intros s; apply funext; intros γ; apply funext; intros x.
  rewrite cat_cmp_cmp; reflexivity.
Defined.

Definition Const {ℙ} (A : Type) : psh ℙ.
Proof.
unshelve econstructor.
+ refine (fun _ => A).
+ refine (fun _ _ _ x => x).
+ reflexivity.
+ reflexivity.
Defined.

Record site (ℙ : cat) := {
  ste_idx : ℙ -> Type;
  ste_obj : forall p (i : ste_idx p), ℙ;
  ste_hom : forall p (i : ste_idx p), ℙ (ste_obj p i) p;
  ste_map : forall p q (α : ℙ q p) (j : ste_idx q), ste_idx p;
  ste_ftr : forall p q (α : ℙ q p) (j : ste_idx q),
    ℙ (ste_obj q j) (ste_obj p (ste_map p q α j));
  ste_eqn : forall p q (α : ℙ q p) j,
    ste_hom q j ∘ α = ste_ftr p q α j ∘ ste_hom p (ste_map p q α j);
}.

Arguments ste_idx {_}.
Arguments ste_obj {_}.
Arguments ste_hom {_}.

Definition compatible {ℙ : cat} (A : psh ℙ) (J : site ℙ)
  {p} (s : forall (i : ste_idx J p), A (ste_obj J p i)) :=
  forall (i₁ i₂ : ste_idx J p) q
      (α₁ : ℙ q (ste_obj J p i₁))
      (α₂ : ℙ q (ste_obj J p i₂)),
      α₁ ∘ ste_hom J p i₁ = α₂ ∘ ste_hom J p i₂ ->
      θ A α₁ (s i₁) = θ A α₂ (s i₂).

Record isSheaf {ℙ : cat} (A : psh ℙ) (J : site ℙ) := {
  shf_elt : forall (p : ℙ)
    (s : forall (i : ste_idx J p), A (ste_obj J p i)), compatible A J s -> A p;
  shf_spc : forall p s sc (i : ste_idx J p),
    θ A (ste_hom J p i) (shf_elt p s sc) = s i;
  shf_unq : forall p s sc (x : A p), (forall i, θ A (ste_hom J p i) x = s i) ->
    x = shf_elt p s sc;
}.

Lemma isSheaf_hProp : forall (ℙ : cat) (A : psh ℙ) (J : site ℙ)
  (is₁ is₂ : isSheaf A J), is₁ = is₂.
Proof.
intros ℙ A J [e₁ s₁ u₁] [e₂ s₂ u₂].
assert (rw : e₁ = e₂).
{ apply funext; intros p; apply funext; intros s; apply funext; intros Hs.
  apply u₂; intros i.
  apply s₁. }
destruct rw.
assert (rw : s₁ = s₂) by apply pi; destruct rw.
assert (rw : u₁ = u₂) by apply pi; destruct rw.
reflexivity.
Qed.

Definition site_id (ℙ : cat) : site ℙ.
Proof.
unshelve refine (Build_site _ _ _ _ _ _ _).
+ refine (fun _ => unit).
+ refine (fun p _ => p).
+ refine (fun p _ => id p).
+ constructor.
+ refine (fun p q α i => α).
+ cbn; intros.
  rewrite cat_cmp_l, cat_cmp_r; reflexivity.
Defined.

Lemma id_sheaf : forall ℙ (A : psh ℙ), isSheaf A (site_id ℙ).
Proof.
intros ℙ A. unshelve econstructor; cbn.
+ intros p s sc; apply (s tt).
+ cbn; intros p s sc [].
  rewrite psh_mon_id; reflexivity.
+ cbn; intros p s sc x Hx.
  rewrite <- Hx, psh_mon_id; reflexivity.
Defined.

Lemma Arr_sheaf_compatible : forall (ℙ : cat) (A B : psh ℙ) (J : site ℙ),
  isSheaf B J ->
  forall (p : ℙ) (s : forall i : ste_idx J p, Arr A B (ste_obj J p i)),
  compatible (Arr A B) J s ->
  forall (q : ℙ) (α : ℙ q p) (x : A q),
  compatible B J
    (fun i : ste_idx J q =>
     nat_fun (s (ste_map _ J p q α i)) (ste_obj J q i)
       (ste_ftr _ J p q α i) (θ A (ste_hom J q i) x)).
Proof.
intros ℙ A B J HB p s Hs q α x i₁ i₂ r α₁ α₂ e.
rewrite (nat_nat (s (ste_map _ J p q α i₁))).
rewrite (nat_nat (s (ste_map _ J p q α i₂))).
rewrite <- !psh_mon_cmp, e.
pose (β₁ := J.(ste_ftr _) _ _ α i₁).
pose (β₂ := J.(ste_ftr _) _ _ α i₂).
unshelve refine (let Hs' := Hs _ _ _ (α₁ ∘ β₁) (α₂ ∘ β₂) _ in _).
{ rewrite !cat_cmp_cmp; unfold β₁, β₂.
rewrite <- !ste_eqn; rewrite <- !cat_cmp_cmp; f_equal.
apply e. }
clearbody Hs'.
apply eq_nat_fun in Hs'; cbn in Hs'.
apply (f_equal (fun f => f r)) in Hs'.
apply (f_equal (fun f => f (id r))) in Hs'.
apply (f_equal (fun f => f ((θ A (α₂ ∘ ste_hom J q i₂) x)))) in Hs'.
rewrite !cat_cmp_l in Hs'.
apply Hs'.
Qed.

Lemma Arr_sheaf : forall ℙ (A B : psh ℙ) J, isSheaf B J -> isSheaf (Arr A B) J.
Proof.
intros ℙ A B J HB.
unshelve econstructor.
+ intros p c Hc. unshelve econstructor.
  - intros q α x.
    unshelve refine (HB.(shf_elt _ _) _ _ _).
    * unshelve refine (fun i => nat_fun (c (J.(ste_map _) p q α i)) (ste_obj J q i) _ (θ A (J.(ste_hom) q i) x)).
      refine (J.(ste_ftr _) _ _ _ _).
    * apply Arr_sheaf_compatible; assumption.
  - intros q r α β x; cbn.
    eapply shf_unq; intros i.
    rewrite <- !psh_mon_cmp.
    rewrite ste_eqn.
    rewrite (psh_mon_cmp _ B).
    rewrite shf_spc.
    rewrite (nat_nat (c (ste_map _ J p q α (ste_map _ J q r β i)))).
    rewrite <- psh_mon_cmp.
    match goal with [ |- nat_fun (c ?i) _ ?α ?x = nat_fun (c ?j) _ ?β _ ] =>
      specialize (Hc i j _ α β);
      refine (let Hc' e := f_equal (fun f => nat_fun f _ (id _) x) (Hc e) in _);
      clearbody Hc'; clear Hc; rename Hc' into Hc; cbn in Hc
    end.
    rewrite !cat_cmp_l in Hc.
    apply Hc.
    rewrite cat_cmp_cmp, <- !ste_eqn.
    rewrite <- cat_cmp_cmp, <- !ste_eqn. apply cat_cmp_cmp.
+ intros p c Hc i; apply nat_fun_eq; cbn.
  apply funext; intros q.
  apply funext; intros α.
  apply funext; intros x.
  symmetry; apply shf_unq; intros j.
  rewrite nat_nat.
  match goal with [ |- nat_fun (c ?i) _ ?α ?x = nat_fun (c ?j) _ ?β _ ] =>
    specialize (Hc i j _ α β)
  end.
  refine (let Hc' e x := f_equal (fun f => nat_fun f _ (id _) x) (Hc e) in _);
  clearbody Hc'; clear Hc; rename Hc' into Hc; cbn in Hc.
  rewrite !cat_cmp_l in Hc.
  apply Hc.
  rewrite cat_cmp_cmp, <- !ste_eqn; reflexivity.
+ intros p c Hc [f Hf] Hu; cbn.
  apply nat_fun_eq; cbn in *.
  refine (let Hu' i q α x := f_equal (fun f => nat_fun f q α x) (Hu i) in _);
  clearbody Hu'; clear Hu; rename Hu' into Hu; cbn in Hu.
  apply funext; intros q.
  apply funext; intros α.
  apply funext; intros x.
  apply shf_unq; intros i.
  rewrite Hf.
  rewrite ste_eqn.
  rewrite Hu; reflexivity.
Defined.

Module Cover.

Record cover {ℙ} (A : psh ℙ) (J : site ℙ) (p : ℙ) := {
  cov_fam : forall (i : ste_idx J p), A (ste_obj J p i);
  cov_cov : compatible A J cov_fam;
}.

Arguments cov_fam {_ _ _ _}.
Arguments cov_cov {_ _ _ _}.

Lemma cov_fam_eq : forall ℙ (A : psh ℙ) J p (c₁ c₂ : cover A J p),
  (forall (i : ste_idx J p), cov_fam c₁ i = cov_fam c₂ i) -> c₁ = c₂.
Proof.
intros.
destruct c₁ as [c₁ Hc₁].
destruct c₂ as [c₂ Hc₂].
cbn in *.
apply funext in H; destruct H.
replace Hc₁ with Hc₂ by apply pi.
reflexivity.
Qed.

Definition Cover {ℙ} (A : psh ℙ) (J : site ℙ) : psh ℙ.
Proof.
unshelve econstructor.
+ refine (cover A J).
+ intros p q α [c Hc]; unshelve econstructor.
  - refine (fun i => θ A (ste_ftr _ J p q α i) (c (J.(ste_map _) _ _ α i))).
  - intros i₁ i₂ r β₁ β₂ H.
    rewrite <- !psh_mon_cmp.
    apply Hc.
    rewrite !cat_cmp_cmp, <- !ste_eqn, <- !cat_cmp_cmp, H; reflexivity.
+ intros p [c Hc]; apply cov_fam_eq; cbn; intros i.
  rewrite <- psh_mon_id.
  apply Hc.
  rewrite <- ste_eqn, cat_cmp_l, cat_cmp_r; reflexivity.
+ intros p q r α β [c Hc]; apply cov_fam_eq; cbn; intros i.
  rewrite <- psh_mon_cmp.
  apply Hc.
  rewrite <- !ste_eqn, cat_cmp_cmp, <- !ste_eqn, <- !cat_cmp_cmp, <- !ste_eqn.
  reflexivity.
Defined.

Definition η {ℙ : cat} (A : psh ℙ) J p : nat A (Cover A J) p.
Proof.
unshelve econstructor; cbn.
+ intros q α x.
  unshelve econstructor.
  - refine (fun i => θ A (J.(ste_hom) _ i) x).
  - intros i₁ i₂ r β₁ β₂ e.
    rewrite <- !psh_mon_cmp, e; reflexivity.
+ intros q r α β x; apply cov_fam_eq; cbn; intros i.
  rewrite <- !psh_mon_cmp, ste_eqn; reflexivity.
Defined.

(* BORKEN
Definition μ {ℙ : cat} (A : psh ℙ) J p : nat (Cover (Cover A J) J) (Cover A J) p.
Proof.
unshelve econstructor; cbn.
+ intros q α x.
  unshelve econstructor.
  - intros i.
    destruct x as [x _]; specialize (x i); cbn in x.
    destruct x as [x _].
    unshelve refine (θ A _ (cov_fam (cov_fam x i) _)).
    * refine (J.(ste_map _) _ _ _ i).
      shelve.
    * apply ste_ftr.
  - intros i₁ i₂ r β₁ β₂ e; cbn.
    rewrite <- !psh_mon_cmp.
*)

Record glue {ℙ : cat} (A : psh ℙ) (J : site ℙ) {p} (c : Cover A J p) := {
  glu_elt : A p;
  glu_spc : forall (i : ste_idx J p), θ A (ste_hom J p i) glu_elt = cov_fam c i;
  glu_unq : forall (x : A p), (forall i, θ A (ste_hom J p i) x = cov_fam c i) -> x = glu_elt;
}.

Lemma glue_η : forall ℙ (A : psh ℙ) J p (x : A p)
  (g : glue A J (η A J p p (id _) x)),
  x = g.(glu_elt _ _ _).
Proof.
intros.
apply glu_unq; intros i; cbn.
reflexivity.
Qed.

End Cover.


Record pfs (ℙ : cat) := {
  pfs_obj : ℙ -> Type;
  pfs_rlz : forall p, (forall q (α : ℙ q p), pfs_obj q) -> Prop; 
}.

Arguments pfs_obj {_}.
Arguments pfs_rlz {_}.

Coercion pfs_obj : pfs >-> Funclass.

Record pEl {ℙ} (A : pfs ℙ) (p : ℙ) := {
  pel_elt : forall q (α : ℙ q p), A q;
  pel_rlz : forall q (α : ℙ q p), A.(pfs_rlz) q (fun r β => pel_elt r (β ∘ α));
}.

Arguments pel_elt {_ _ _}.
Arguments pel_rlz {_ _ _}.

Lemma pel_elt_eq : forall ℙ A p (x y : @pEl ℙ A p),
  (forall q α, x.(pel_elt) q α = y.(pel_elt) q α) -> x = y.
Proof.
intros ℙ A p [x xε] [y yε] e.
cbn in e.
assert (e' : x = y).
{ apply funext; intros q; apply funext; intros α; apply e. }
destruct e'.
replace xε with yε by apply pi.
reflexivity.
Qed.

Definition lift_pEl {ℙ : cat} {A p q} (α : ℙ q p) (x : @pEl ℙ A p): pEl A q.
Proof.
unshelve refine (Build_pEl _ _ _ _ _).
+ refine (fun r β => x.(pel_elt) r (β ∘ α)).
+ intros r β; cbn.
  replace (fun s γ => pel_elt x s ((γ ∘ β) ∘ α)) with (fun s γ => pel_elt x s (γ ∘ (β ∘ α))).
  - refine (x.(pel_rlz) _ _).
  - apply funext; intros s; apply funext; intros γ; rewrite cat_cmp_cmp; reflexivity.
Defined.

Definition to_psh {ℙ} (A : pfs ℙ) : psh ℙ.
Proof.
unshelve econstructor.
+ refine (pEl A).
+ refine (fun p q α x => lift_pEl α x).
+ intros p x.
  apply pel_elt_eq; intros q α.
  cbn; rewrite cat_cmp_r; reflexivity.
+ intros p q r α β x; apply pel_elt_eq; intros s γ; cbn.
  rewrite cat_cmp_cmp; reflexivity.
Defined.

Definition pfs_compatible {ℙ : cat} (A : pfs ℙ) (J : site ℙ)
  {p}
  (s : forall (i : ste_idx J p) q (α : ℙ q (ste_obj J p i)), A q)
  (sε : forall (i : ste_idx J p) q (α : ℙ q (ste_obj J p i)),
      A.(pfs_rlz) q (fun r β => s i _ (β ∘ α)))
  :=
  forall (i₁ i₂ : ste_idx J p) q
      (α₁ : ℙ q (ste_obj J p i₁))
      (α₂ : ℙ q (ste_obj J p i₂)),
      α₁ ∘ ste_hom J p i₁ = α₂ ∘ ste_hom J p i₂ ->
      s i₁ q α₁ = s i₂ q α₂.

Record isFascist {ℙ : cat} (A : pfs ℙ) (J : site ℙ) (p : ℙ) := {
  fsc_elt : forall s sε (sc : @pfs_compatible _ A J p s sε) q (α : ℙ q p), A q;
  fsc_rlz : forall s sε (sc : @pfs_compatible _ A J p s sε),
    forall q (α : ℙ q p), A.(pfs_rlz) q (fun r β => fsc_elt s sε sc r (β ∘ α));
  fsc_spc : forall s sε sc (i : ste_idx J p) q (α : ℙ q _),
    fsc_elt s sε sc q (α ∘ ste_hom J p i) = s i q α;
  fsc_unq : forall s sε sc (x : pEl A p),
    (forall i q (α : ℙ q _),
      x.(pel_elt) q (α ∘ ste_hom J p i) = s i q α) ->
    forall q (α : ℙ q p),
    x.(pel_elt) q α = fsc_elt s sε sc q α;
}.

(*
Record isFascist {ℙ : cat} (A : pfs ℙ) (J : site ℙ) := {
  fsc_elt : forall (p : ℙ) s sε (sc : @pfs_compatible _ A J p s sε) q (α : ℙ q p), A q;
  fsc_rlz : forall (p : ℙ) s sε (sc : @pfs_compatible _ A J p s sε),
    forall q (α : ℙ q p), A.(pfs_rlz) q (fun r β => fsc_elt p s sε sc r (β ∘ α));
  fsc_spc : forall p s sε sc (i : ste_idx J p) q (α : ℙ q _),
    fsc_elt p s sε sc q (α ∘ ste_hom J p i) = s i q α;
  fsc_unq : forall p s sε sc (x : pEl A p),
    (forall i q (α : ℙ q _),
      x.(pel_elt) q (α ∘ ste_hom J p i) = s i q α) ->
    forall q (α : ℙ q p),
    x.(pel_elt) q α = fsc_elt p s sε sc q α;
}.
*)
(*
Lemma isSheaf_isFascist : forall ℙ (A : pfs ℙ) (J : site ℙ),
  isFascist A J -> isSheaf (to_psh A) J.
Proof.
intros ℙ A J HA.
unshelve econstructor.
+ intros p c Hc.
  unshelve econstructor.
  -   

*)

Module PreList.

Require Import List.

Definition ℙ : cat.
Proof.
unshelve econstructor.
+ refine (list bool).
+ refine (fun p q => exists l, p = app l q).
+ intros p; exists nil; reflexivity.
+ cbn; intros p q r [l₁ Hl₁] [l₂ Hl₂].
  exists (app l₁ l₂).
  rewrite Hl₁, Hl₂.
  apply app_assoc.
+ intros; apply pi.
+ intros; apply pi.
+ intros; apply pi.
Defined.

Definition site_split : site ℙ.
Proof.
unshelve econstructor; cbn.
6: { intros. apply pi. }
+ refine (fun p => match p with nil => False | cons _ _ => bool end).
+ refine (fun p i => _).

+ cbn.
  intros p i. apply PeanoNat.Nat.le_pred_l.
+ intros p q α i; cbn in *.
  destruct p.
  destruct q; [assumption|inversion α].
  exact tt.
+ cbn. intros p q α i.
  apply PeanoNat.Nat.pred_le_mono, α.
Defined.

End PreList.

Module Nat.

Require Arith.

Definition ℙ : cat.
Proof.
unshelve econstructor.
+ refine Datatypes.nat.
+ refine (fun p q => le p q).
+ intros p. apply le_n.
+ cbn; intros p q r α β; etransitivity; eassumption.
+ intros; apply pi.
+ intros; apply pi.
+ intros; apply pi.
Defined.

Definition site_split : site ℙ.
Proof.
unshelve econstructor; cbn.
6: { intros. apply pi. }
+ refine (fun p => match p with O => False | S n => unit end).
+ refine (fun p i => pred p).
+ cbn.
  intros p i. apply PeanoNat.Nat.le_pred_l.
+ intros p q α i; cbn in *.
  destruct p.
  destruct q; [assumption|inversion α].
  exact tt.
+ cbn. intros p q α i.
  apply PeanoNat.Nat.pred_le_mono, α.
Defined.

End PreList.
