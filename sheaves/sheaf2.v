Axiom funext : forall A (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.
Axiom pi : forall (A : Prop) (p q : A), p = q.

Lemma fapp : forall {A} (x : A) {B : A -> Type} (f g : forall x, B x),
  f = g -> f x = g x.
Proof.
intros ? ? ? ? ? []; reflexivity.
Qed.

Definition proof {A : Prop} {x : A} : A := x.

Ltac hide := refine (@proof _ _).

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

Record Elt {ℙ : cat} (A : psh ℙ) := {
  elt_fun : forall (p : ℙ), A p; 
  elt_nat : forall p q (α : ℙ q p),
    θ A α (elt_fun p) = elt_fun q;
}.

Record Hom {ℙ} (A B : psh ℙ) := {
  hom_fun : forall (p : ℙ), A p -> B p;
  hom_nat : forall p q (α : ℙ q p) (x : A p),
    hom_fun q (θ A α x) = θ B α (hom_fun p x);
}.

Arguments hom_fun {_ _ _}.
Arguments hom_nat {_ _ _}.

Lemma hom_eq : forall ℙ A B (f g : @Hom ℙ A B),
  (forall p, f.(hom_fun) p = g.(hom_fun) p) -> f = g.
Proof.
intros ℙ A B [f fε] [g gε] e; cbn in *.
assert (e' : f = g).
{ apply funext; intros p.
  apply e. }
destruct e'.
f_equal.
apply pi.
Qed.

Record nat {ℙ : cat} (A B : psh ℙ) (p : ℙ) := {
  nat_fun : forall q (α : ℙ q p), A q -> B q; 
  nat_nat : forall q r (α : ℙ q p) (β : ℙ r q) (x : A q),
    θ B β (nat_fun q α x) = nat_fun r (β ∘ α) (θ A β x)
}.

Arguments nat_fun {_ _ _ _}.
Arguments nat_nat {_ _ _ _}.

Coercion nat_fun : nat >-> Funclass.

Lemma nat_fun_eq : forall ℙ A B p (f g : @nat ℙ A B p),
  (forall q (α : ℙ q p) (x : A q), f.(nat_fun) q α x = g.(nat_fun) q α x) -> f = g.
Proof.
intros ℙ A B p [f Hf] [g Hg] e; cbn in *.
assert (e' : f = g).
{ apply funext; intros q; apply funext; intros α; apply funext; intros x.
  apply e. }
destruct e'.
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
  - hide; intros r s β γ x; cbn in *.
    rewrite cat_cmp_cmp.
    apply (f.(nat_nat)).
+ hide. cbn; intros p [f Hf].
  apply nat_fun_eq; cbn.
  intros q α x.
  rewrite cat_cmp_r; reflexivity.
+ hide. intros p q r α β [f Hf]; cbn in *. 
  apply nat_fun_eq; cbn.
  intros s γ x.
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

Record sieve {ℙ : cat} (p : ℙ) := {
  sve_fun : forall q (α : ℙ q p), Prop;
  sve_mon : forall q (α : ℙ q p) r (β : ℙ r q), sve_fun q α -> sve_fun r (β ∘ α);
}.

Arguments sve_fun {_ _} _ {_}.
Arguments sve_mon {_ _} _ {_} _ {_}.

Notation "α ∈ s" := (sve_fun s α) (at level 10).

Definition sieve_top {ℙ : cat} {p : ℙ} : sieve p.
Proof.
unshelve econstructor.
+ refine (fun _ _ => True).
+ cbn; constructor.
Defined.

Definition sieve_mon {ℙ : cat} {p : ℙ} (s : sieve p) {q} (α : ℙ q p) : sieve q.
Proof.
unshelve econstructor.
+ refine (fun r β => s.(sve_fun) (β ∘ α)).
+ cbn; intros r β t γ H.
  rewrite cat_cmp_cmp; apply sve_mon, H.
Defined.

Lemma sieve_eq : forall {ℙ : cat} (p : ℙ) (s₁ s₂ : sieve p),
  (forall q (α : ℙ q p), sve_fun s₁ α = sve_fun s₂ α) -> s₁ = s₂.
Proof.
intros ℙ p [s₁ sc₁] [s₂ sc₂] e.
assert (rw : s₁ = s₂).
{ apply funext; intros q; apply funext; intros α; apply e. }
destruct rw.
assert (rw : sc₁ = sc₂) by apply pi.
destruct rw; reflexivity.
Qed.

Lemma sieve_mon_cmp : forall {ℙ : cat} {p : ℙ} (s : sieve p) {q} (α : ℙ q p) {r} (β : ℙ r q),
  sieve_mon (sieve_mon s α) β = sieve_mon s (β ∘ α).
Proof.
intros.
apply sieve_eq; intros t γ; cbn.
rewrite cat_cmp_cmp; reflexivity.
Qed.

Definition Sieve {ℙ} : psh ℙ.
Proof.
unshelve econstructor.
+ refine sieve.
+ refine (fun p q α s => sieve_mon s α).
+ cbn; intros p [s θs]; unfold sieve_mon; cbn.
  apply sieve_eq; intros q α; cbn.
  rewrite cat_cmp_r; reflexivity.
+ intros p q r α β s; cbn; apply sieve_eq; intros t γ; cbn.
  rewrite cat_cmp_cmp; reflexivity.
Defined.

Record site (ℙ : cat) := {
  ste_sve : forall (p : ℙ), sieve p -> Prop;
  ste_mon : forall (p : ℙ) (s : sieve p) q (α : ℙ q p),
    ste_sve p s -> ste_sve q (sieve_mon s α);
  (** ⊢ J : Prop → Prop *)
  ste_one : forall (p : ℙ), ste_sve p sieve_top;
  (** ⊢ J 1 *)
  ste_cmp : forall (p : ℙ) (s s' : sieve p),
    ste_sve p s ->
    (forall q (α : ℙ q p), α ∈ s -> ste_sve q (sieve_mon s' α)) ->
    ste_sve p s';
  (** ⊢ J A → (A → J B) → J B *)
}.

Arguments ste_sve {_} _ {_}.
Arguments ste_mon {_} _ {_} _ {_} _.

Record cover {ℙ : cat} (A : psh ℙ) {p} (s : sieve p) := {
  cov_fun : forall q (α : ℙ q p), α ∈ s -> A q;
  cov_cmp : forall q (α : ℙ q p) r (β : ℙ r q) (hα : α ∈ s),
    θ A β (cov_fun q α hα) = cov_fun r (β ∘ α) (sve_mon s α β hα);
}.
(** C A s := s → A  *)

Arguments cov_fun {_ _ _ _} _ {_}.

Lemma cover_eq : forall (ℙ : cat) (A : psh ℙ) p (s : sieve p) (c₁ c₂ : cover A s),
  (forall q (α : ℙ q p) (hα : α ∈ s), c₁.(cov_fun) α hα = c₂.(cov_fun) α hα) -> c₁ = c₂.
Proof.
intros ℙ A p s [c₁ hc₁] [c₂ hc₂] e.
assert (rw : c₁ = c₂).
{ apply funext; intros q; apply funext; intros α; apply funext; intros hα.
  apply e. }
destruct rw.
assert (rw : hc₁ = hc₂) by apply pi.
destruct rw; reflexivity.
Qed.

Definition cover_mon {ℙ : cat} (A : psh ℙ) {p : ℙ} (s : sieve p) (c : cover A s)
  {q} (α : ℙ q p) : cover A (sieve_mon s α).
Proof.
unshelve econstructor.
+ refine (fun r β hβ => c.(cov_fun) (β ∘ α) hβ).
+ refine (fun r β t γ hβ => _).
  rewrite cov_cmp.
  cbn.
  match goal with [ |- cov_fun _ _ ?p = _ ] => set (π := p) end; clearbody π.
  match goal with [ |- _ = cov_fun _ _ ?p ] => set (ρ := p) end; clearbody ρ.
  cbn in ρ.
  revert π ρ.
  rewrite cat_cmp_cmp; intros; f_equal; apply pi.
Defined.

Record isSheaf {ℙ : cat} (A : psh ℙ) (J : site ℙ) := {
  shf_elt : forall (p : ℙ) (s : sieve p) (hs : J.(ste_sve) s) (c : cover A s), A p;
  (** ⊢ φ : Π (s : Prop), J s → (s → A) → A *)
  shf_spc : forall p (s : sieve p) (hs : J.(ste_sve) s) (c : cover A s),
    forall q (α : ℙ q p) (hα : α ∈ s),
      θ A α (shf_elt p s hs c) = c.(cov_fun) α hα;
  (** ⊢ Π (s : Prop) (i : J s) (c : s → A) (p : s), φ s i c = c p *)
  shf_unq :
    forall (p : ℙ) (s : sieve p) (hs : J.(ste_sve) s) (c : cover A s) (x : A p),
      (forall q (α : ℙ q p) (hα : α ∈ s), θ A α x = c.(cov_fun) α hα) ->
      x = shf_elt p s hs c;
  (** ⊢ Π (s : Prop) (i : J s) (c : s → A) (x : A), (Π (p : s), x = c p) → x = φ s i c *)
}.

Arguments shf_elt {_ _ _}.
Arguments shf_spc {_ _ _}.
Arguments shf_unq {_ _ _}.

(* Σ (P : Prop), J P × (P → A) *)
Record T_obj {ℙ} (A : psh ℙ) (J : site ℙ) (p : ℙ) := {
  tup_sve : sieve p;
  tup_mod : J.(ste_sve) tup_sve;
  tup_cov : cover A tup_sve;
}.

Definition T {ℙ} (A : psh ℙ) (J : site ℙ) : psh ℙ.
Proof.
unshelve econstructor.
+ intro p.
  refine (T_obj A J p).
+ cbn; intros p q α [s j c].
  exists (sieve_mon s α).
  - apply ste_mon, j.
  - apply cover_mon, c.
+ cbn. intros p [s j c].
  assert (e : s = sieve_mon s (id p)).
  {
    apply sieve_eq; intros q α; cbn.
    rewrite cat_cmp_r; reflexivity.
  }
  assert (ec : match e in _ = s' return cover A s' with eq_refl => c end = cover_mon A s c (id p)).
  { apply cover_eq; intros q α hα.
    destruct c as [c hc]; cbn.
    assert (hα' : α ∈ s).
    { cbn in hα; rewrite cat_cmp_r in hα; exact hα. }
    transitivity (c _ α hα'); [clear|].
    + destruct e; cbn; f_equal; apply pi.
    + revert hα; cbn; rewrite cat_cmp_r; intros hα; f_equal; apply pi.
  }
  destruct ec.
  match goal with [ |- Build_T_obj _ _ _ _ _ ?e _ = _ ] => set (k := e) end.
  clearbody k.
  destruct e.
  replace k with j by apply pi; reflexivity.
+ intros p q r α β [s i c].
  match goal with [ |- Build_T_obj _ _ _ _ _ ?e _ = _ ] => set (j := e); clearbody j end.
  match goal with [ |- _ = Build_T_obj _ _ _ _ _ ?e _ ] => set (k := e); clearbody k end.
  assert (e : sieve_mon (sieve_mon s α) β = sieve_mon s (β ∘ α)).
  { apply sieve_mon_cmp. }
  assert (ec : match e in _ = s' return cover A s' with eq_refl => cover_mon A (sieve_mon s α) (cover_mon A s c α) β end = cover_mon A s c (β ∘ α)).
  {
    clear; apply cover_eq.
    intros t γ hγ; cbn.
    assert (hγ' : ((γ ∘ β) ∘ α) ∈ s).
    { rewrite cat_cmp_cmp; apply hγ. }
    transitivity (cov_fun c ((γ ∘ β) ∘ α) hγ').
    + destruct e; cbn; f_equal; apply pi.
    + clear; revert hγ hγ'; rewrite cat_cmp_cmp; intros.
      f_equal; apply pi.
  }
  destruct ec.
  destruct e.
  assert (ei : j = k) by apply pi; destruct ei.
  reflexivity.
Defined.

Lemma shf_elt_rev {ℙ : cat} (A : psh ℙ) (J : site ℙ) :
  forall (φ : Hom (T A J) A),
  (** ⊢ Π (s : Prop) (i : J s) (c : s → A) (x : A), (Π (p : s), x = c p) → x = φ s i c *)
  (forall (p : ℙ) (s : sieve p) (i : J.(ste_sve) s) (c : cover A s) (x : A p),
      (forall q (α : ℙ q p) (hα : α ∈ s),
        θ A α x = c.(cov_fun) α hα) ->
          x = φ.(hom_fun) p (Build_T_obj _ _ _ _ s i c)) ->
  isSheaf A J.
Proof.
intros φ Hφ.
unshelve econstructor.
+ intros p s i c.
  refine (hom_fun φ p _).
  refine (Build_T_obj _ _ _ _ s i c).
+ refine (fun p s i c q α hα => _); cbn.
  rewrite <- hom_nat; cbn.
  symmetry; apply Hφ.
  intros r β hβ; cbn in *.
  rewrite cov_cmp; f_equal; apply pi.
+ intros p s i c x e; cbn.
  apply Hφ, e.
Defined.

Lemma shf_elt_fun {ℙ : cat} (A : psh ℙ) (J : site ℙ) (hA : isSheaf A J) :
  Hom (T A J) A.
Proof.
unshelve econstructor; cbn.
+ intros p [s i c].
  apply (shf_elt hA _ s i c).
+ intros p q α [s i c]; cbn.
  symmetry; apply shf_unq.
  intros r β hβ.
  rewrite <- psh_mon_cmp.
  assert (e := shf_spc hA _ s i c _ (β ∘ α) hβ).
  rewrite e; clear e.
  reflexivity.
Defined.

Lemma shf_elt_spc {ℙ : cat} (A : psh ℙ) (J : site ℙ) (hA : isSheaf A J) :
  let φ := shf_elt_fun A J hA in
  (forall (p : ℙ) (s : sieve p) (i : J.(ste_sve) s) (c : cover A s) (x : A p),
      (forall q (α : ℙ q p) (hα : α ∈ s),
        θ A α x = c.(cov_fun) α hα) ->
          x = φ.(hom_fun) p (Build_T_obj _ _ _ _ s i c)).
Proof.
cbn; intros p s i c x e.
apply shf_unq, e.
Qed.

Definition cover_η {ℙ : cat} (A : psh ℙ) {p} (s : sieve p) (x : A p) : cover A s.
Proof.
unshelve econstructor.
+ refine (fun q α hα => θ A α x).
+ intros q α r β hα.
  cbn; rewrite psh_mon_cmp; reflexivity.
Defined.

Lemma shf_elt_rev2 {ℙ : cat} (A : psh ℙ) (J : site ℙ) :
  (** ⊢ φ : Π (s : Prop), J s → (s → A) → A *)
  forall (φ : Hom (T A J) A),
  (** ⊢ Π (s : Prop) (i : J s) (x : A), → x = φ s i (λ p : s, x) *)
  (forall (p : ℙ) (s : sieve p) (i : J.(ste_sve) s) (x : A p),
    x = φ.(hom_fun) p (Build_T_obj ℙ _ _ _ s i (cover_η A s x))) ->
  isSheaf A J.
Proof.
intros φ Hφ.
unshelve econstructor.
+ intros p s i c.
  refine (hom_fun φ p _).
  refine (Build_T_obj _ _ _ _ s i c).
+ refine (fun p s i c q α hα => _); cbn.
  rewrite <- hom_nat; cbn.
  match goal with [ |- ?x = _ ] =>
  rewrite (Hφ _ (sieve_mon s α) (J.(ste_mon) s α i))
  end.
  assert (e : cover_mon A s c α = cover_η A (sieve_mon s α) (cov_fun c α hα)).
  { clear; apply cover_eq; intros r β hβ; cbn.
    rewrite cov_cmp; f_equal; apply pi. }
  destruct e; reflexivity.
+ intros p s i c x e; cbn.
  etransitivity; [apply (Hφ p s i x)|].
  repeat f_equal.
  apply cover_eq; intros q α hα; apply e.
Defined.

Lemma isSheaf_hProp : forall (ℙ : cat) (A : psh ℙ) (J : site ℙ)
  (is₁ is₂ : isSheaf A J), is₁ = is₂.
Proof.
intros ℙ A J [e₁ s₁ u₁] [e₂ s₂ u₂].
assert (rw : e₁ = e₂).
{ apply funext; intros p; apply funext; intros f; apply funext; intros s; apply funext; intros Hs.
  apply u₂; intros i.
  apply s₁. }
destruct rw.
assert (rw : s₁ = s₂) by apply pi; destruct rw.
assert (rw : u₁ = u₂) by apply pi; destruct rw.
reflexivity.
Qed.

Definition site_id (ℙ : cat) : site ℙ.
Proof.
unshelve refine (Build_site _ _ _ _ _).
+ refine (fun p s => forall q (α : ℙ q p), s.(sve_fun) α).
+ cbn; intros p s q α hs r β.
  apply hs.
+ constructor.
+ cbn; intros p s s' hs f q α.
  specialize (f q α (hs q α) q (id _)).
  rewrite cat_cmp_l in f; apply f.
Defined.

Lemma id_sheaf : forall ℙ (A : psh ℙ), isSheaf A (site_id ℙ).
Proof.
intros ℙ A. unshelve econstructor; cbn.
+ intros p s hs c.
  apply (c.(cov_fun) (id p) (hs _ _)).
+ cbn; intros p s hs c q α hα.
  rewrite cov_cmp; cbn.
  set (hα' := sve_mon s (id p) α (hs p (id p))); clearbody hα'.
  revert hα'.
  rewrite cat_cmp_r; intros.
  replace hα' with hα by apply pi; reflexivity.
+ cbn; intros p s hs c x hx.
  rewrite <- hx, psh_mon_id; reflexivity.
Defined.

Lemma Arr_sheaf : forall ℙ (A B : psh ℙ) J, isSheaf B J -> isSheaf (Arr A B) J.
Proof.
intros ℙ A B J HB.
unshelve refine (shf_elt_rev2 _ _ _ _); [unshelve econstructor|].
+ intros p [s i c].
  unshelve econstructor.
  - intros q α x.
    unshelve refine (HB.(shf_elt) _ (sieve_mon s α) (ste_mon _ _ _ i) _).
    unshelve econstructor.
    * intros r β hβ; cbn in *.
      refine (c.(cov_fun) _ hβ _ (id _) (θ A β x)).
    * intros r β t γ hα; cbn in *.
      match goal with [ |- context [ cov_fun c ((γ ∘ β) ∘ α) ?e ] ] => set (π := e); clearbody π end.
      cbn in *.
      rewrite !nat_nat, <- !psh_mon_cmp.
      rewrite cat_cmp_r.
      revert π; rewrite cat_cmp_cmp; intros π.
      assert (e := c.(cov_cmp _ _) _ (β ∘ α) _ γ hα).
      cbn in e.
      replace π with (sve_mon s (β ∘ α) γ hα) by apply pi.
      rewrite <- e; cbn.
      rewrite cat_cmp_l; reflexivity.
  - intros q r α β x; cbn.
    try (is_var (sieve p); fail 1).
    match goal with [ |- context [ Build_cover _ _ _ _ _ ?e ] ] => set (π := e); clearbody π; cbn in π end.
    apply shf_unq; cbn.
    intros t γ hγ.
    rewrite <- !psh_mon_cmp.
    assert (hγ' : ((γ ∘ β) ∘ α) ∈ s).
    { rewrite cat_cmp_cmp; assumption. }
    match goal with [ |- context [ shf_elt HB _ ?s ?i ?c ] ] =>
      assert (e := HB.(shf_spc) _ s i c _ _ hγ')
    end.
  rewrite e; clear e; cbn.
  revert hγ hγ'; rewrite cat_cmp_cmp; intros.
  replace hγ with hγ' by apply pi; reflexivity.
+ intros p q α [s i c].
  apply nat_fun_eq; cbn.
  intros r β x.
  match goal with [ |- context [ shf_elt _ _ _ _ ?e ] ] => try (is_var e; fail 1); set (c1 := e) end.
  assert (e1 : @cov_fun _ _ _ _ c1 = @cov_fun _ _ _ _ c1) by reflexivity.
  unfold c1 at 2 in e1; clearbody c1; cbn in e1.
  match goal with [ |- context [ shf_elt _ _ _ _ ?e ] ] => try (is_var e; fail 1); set (c2 := e) end.
  assert (e2 : @cov_fun _ _ _ _ c2 = @cov_fun _ _ _ _ c2) by reflexivity.
  unfold c2 at 2 in e2; clearbody c2; cbn in e2.
  match goal with [ |- context [ shf_elt _ _ _ ?e _ ] ] => try (is_var e; fail 1); set (i1 := e); clearbody i1 end.
  match goal with [ |- context [ shf_elt _ _ _ ?e _ ] ] => try (is_var e; fail 1); set (i2 := e); clearbody i2 end.
  assert (e := sieve_mon_cmp s α β).
  assert (e' : match e in _ = s return cover B s with eq_refl => c1 end = c2).
  { clear - e1 e2. apply cover_eq; intros t γ hγ.
    rewrite e2.
    assert (hγ' : γ ∈ (sieve_mon (sieve_mon s α) β)).
    { rewrite e; assumption. }
    transitivity (cov_fun c ((γ ∘ β) ∘ α) hγ' t (id t) (θ A γ x)).
    + clear - e1; revert hγ hγ'; destruct e; intros hγ hγ'.
      rewrite e1.
      replace hγ with hγ' by apply pi; reflexivity.
    + clear. revert hγ hγ'; cbn; rewrite cat_cmp_cmp; intros.
      replace hγ with hγ' by apply pi; reflexivity.
  }
  clear - e'.
  destruct e, e'.
  f_equal; apply pi.
+ intros p s i [f fε]; cbn.
  apply nat_fun_eq; intros q α x; cbn.
  match goal with [ |- context [ shf_elt _ _ _ _ ?e ] ] => try (is_var e; fail 1); set (c := e) end.
  assert (e : @cov_fun _ _ _ _ c = @cov_fun _ _ _ _ c) by reflexivity.
  unfold c at 2 in e; clearbody c; cbn in e.
  apply shf_unq; intros r β hβ.
  rewrite e, cat_cmp_l.
  apply fε.
Defined.
