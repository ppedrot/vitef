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
  - hide; intros r s β γ x; cbn in *.
    rewrite cat_cmp_cmp.
    apply (f.(nat_nat)).
+ hide. cbn; intros p [f Hf].
  apply nat_fun_eq; cbn.
  apply funext; intros q; apply funext; intros α; apply funext; intros x.
  rewrite cat_cmp_r; reflexivity.
+ hide. intros p q r α β [f Hf]; cbn in *. 
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
  ste_fam : ℙ -> Type;
  ste_idx : forall (p : ℙ), ste_fam p -> Type;
  ste_obj : forall p f (i : ste_idx p f), ℙ;
  ste_hom : forall p f (i : ste_idx p f), ℙ (ste_obj p f i) p;
  ste_fun : forall p q (α : ℙ q p), ste_fam p -> ste_fam q;
  ste_map : forall p q (α : ℙ q p) f (j : ste_idx q (ste_fun _ _ α f)), ste_idx p f;
  ste_ftr : forall p q (α : ℙ q p) f (j : ste_idx q (ste_fun _ _ α f)),
    ℙ (ste_obj q (ste_fun p q α f) j) (ste_obj p f (ste_map p q α f j));
  ste_eqn : forall p q (α : ℙ q p) (f : ste_fam p) j,
    ste_hom q (ste_fun p q α f) j ∘ α = ste_ftr p q α f j ∘ ste_hom p f (ste_map p q α f j);
}.

Arguments ste_fam {_}.
Arguments ste_idx {_}.
Arguments ste_obj {_}.
Arguments ste_hom {_}.
Arguments ste_fun {_} _ {_ _}.
Arguments ste_map {_} _ {_ _}.
Arguments ste_ftr {_} _ {_ _}.

Definition cover {ℙ : cat} (A : psh ℙ) {J : site ℙ}
  {p} (f : ste_fam J p) := forall (i : ste_idx J p f), A (ste_obj J p f i).

Definition compatible {ℙ : cat} (A : psh ℙ) (J : site ℙ)
  {p} (f : ste_fam J p) (s : cover A f) :=
  forall (i₁ i₂ : ste_idx J p f) q
      (α₁ : ℙ q (ste_obj J p f i₁))
      (α₂ : ℙ q (ste_obj J p f i₂)),
      α₁ ∘ ste_hom J p f i₁ = α₂ ∘ ste_hom J p f i₂ ->
      θ A α₁ (s i₁) = θ A α₂ (s i₂).

Record isSheaf {ℙ : cat} (A : psh ℙ) (J : site ℙ) := {
  shf_elt : forall (p : ℙ) (f : ste_fam J p)
    (s : cover A f), compatible A J f s -> A p;
  shf_spc : forall p (f : ste_fam J p) s sc (i : ste_idx J p f),
    θ A (ste_hom J p f i) (shf_elt p f s sc) = s i;
  shf_unq : forall p f s sc (x : A p), (forall i, θ A (ste_hom J p f i) x = s i) ->
    x = shf_elt p f s sc;
}.

Arguments shf_elt {_ _ _}.
Arguments shf_spc {_ _ _}.
Arguments shf_unq {_ _ _}.

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
unshelve refine (Build_site _ _ _ _ _ _ _ _ _).
+ refine (fun _ => unit).
+ refine (fun _ _ => unit).
+ refine (fun p _ _ => p).
+ refine (fun p _ _ => id p).
+ constructor.
+ constructor.
+ refine (fun p q α f i => α).
+ cbn; intros.
  rewrite cat_cmp_l, cat_cmp_r; reflexivity.
Defined.

Lemma id_sheaf : forall ℙ (A : psh ℙ), isSheaf A (site_id ℙ).
Proof.
intros ℙ A. unshelve econstructor; cbn.
+ intros p f s sc; apply (s tt).
+ cbn; intros p f s sc [].
  rewrite psh_mon_id; reflexivity.
+ cbn; intros p f s sc x Hx.
  rewrite <- Hx, psh_mon_id; reflexivity.
Defined.

Lemma cover_mon {ℙ : cat} {A : psh ℙ} {J : site ℙ}
  {p : ℙ} (f : ste_fam J p) (s : cover A f) {q} (α : ℙ q p) : cover A (ste_fun J α f).
Proof.
refine (fun j => θ A (ste_ftr J _ _ j) (s (ste_map J α f j))).
Defined.

Definition App_cover {ℙ : cat} {A B : psh ℙ} {J : site ℙ}
  {p : ℙ} (f : ste_fam J p) (s : cover (Arr A B) f)
  (q : ℙ) (α : ℙ q p) (x : A q) : cover B (ste_fun J α f) :=
  fun i : ste_idx J q _ =>
     s (ste_map J α f i) (ste_obj J q _ i)
       (ste_ftr J α f i) (θ A (ste_hom J q _ i) x).

Lemma App_cover_compatible : forall {ℙ : cat} {A B : psh ℙ} {J : site ℙ},
  forall {p : ℙ} {f} (s : cover (Arr A B) f),
  compatible (Arr A B) J f s ->
  forall (q : ℙ) (α : ℙ q p) (x : A q),
  compatible B J (ste_fun J α f) (App_cover f s q α x).
Proof.
intros ℙ A B J p f s Hs q α x i₁ i₂ r α₁ α₂ e.
unfold App_cover.
rewrite (nat_nat (s (ste_map J α f i₁))).
rewrite (nat_nat (s (ste_map J α f i₂))).
rewrite <- !psh_mon_cmp, e.
pose (β₁ := J.(ste_ftr) α f i₁).
pose (β₂ := J.(ste_ftr) α f i₂).
unshelve refine (let Hs' := Hs _ _ _ (α₁ ∘ β₁) (α₂ ∘ β₂) _ in _).
{ rewrite !cat_cmp_cmp; unfold β₁, β₂.
rewrite <- !ste_eqn; rewrite <- !cat_cmp_cmp; f_equal.
apply e. }
clearbody Hs'.
apply eq_nat_fun in Hs'; cbn in Hs'.
apply (f_equal (fun f => f r)) in Hs'.
apply (f_equal (fun f => f (id r))) in Hs'.
apply (f_equal (fun f => f ((θ A (α₂ ∘ ste_hom J q _ i₂) x)))) in Hs'.
rewrite !cat_cmp_l in Hs'.
apply Hs'.
Qed.

Lemma Arr_sheaf : forall ℙ (A B : psh ℙ) J, isSheaf B J -> isSheaf (Arr A B) J.
Proof.
intros ℙ A B J HB.
unshelve econstructor.
+ intros p f s Hs. unshelve econstructor.
  - intros q α x.
    unshelve refine (HB.(shf_elt) _ (ste_fun J α f) _ _).
    * unshelve refine (App_cover f s q α x).
    * apply App_cover_compatible; assumption.
  - intros q r α β x; cbn.

    assert (Hs' : compatible B J (ste_fun J (β ∘ α) f)
      (App_cover f s r (β ∘ α) (θ A β x))).
    {
      intros i₁ i₂ t α₁ α₂ e.
      unfold App_cover.
      rewrite !nat_nat, <- !psh_mon_cmp, e.
      unfold compatible in Hs.
      cbn in Hs.
      specialize (Hs (ste_map J _ f i₁) (ste_map J _ f i₂) _
        (α₁ ∘ ste_ftr J (β ∘ α) f i₁) (α₂ ∘ ste_ftr J (β ∘ α) f i₂)).
      apply eq_nat_fun in Hs; cbn in Hs.
      2: {
        rewrite !cat_cmp_cmp, <- !ste_eqn, <- !cat_cmp_cmp, e; reflexivity. 
      }
      apply (fapp t) in Hs.
      apply (fapp (id _)) in Hs.
      match goal with [ |- _ ?x = _ ] => apply (fapp x) in Hs end.
      rewrite !cat_cmp_l in Hs; apply Hs.
    }
    unshelve match goal with [ |- ?e = _ ] =>
      replace e with (shf_elt HB r (ste_fun J (β ∘ α) f) (App_cover _ s  _ _ (θ A β x)) Hs')
    end.
    { apply f_equal, pi. }
    symmetry.
   apply shf_unq; intros i.
Abort.
(*

    assert (rw := J.(ste_eqn _) _ _ (β ∘ α) f i).

    rewrite <- (nat_nat (s (ste_map J (β ∘ α) f i))).
  

    rewrite ste_eqn.
    rewrite <- !psh_mon_cmp.
    rewrite <- (nat_nat (s (ste_map J (β ∘ α) f i))).

    rewrite <- (B.(shf_spc) J HB _ _
      (App_cover f s r (β ∘ α) (θ A β x))
      (Arr_sheaf_compatible _ _ _ _ HB _ _ _ Hs _ _ _)
    ).
    rewrite (psh_mon_cmp _ B).
    f_equal.
    eapply shf_unq; intros j.
    rewrite <- (psh_mon_cmp _ B).
    

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
*)

(*
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
*)

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

Lemma pEl_eq : forall ℙ A p (x y : @pEl ℙ A p),
  (forall q α, x.(pel_elt) q α = y.(pel_elt) q α) -> x = y.
Proof.
intros ℙ A p [x xε] [y yε] e; cbn in *.
assert (rw : x = y).
{ apply funext; intros; apply funext; intros; apply e. }
destruct rw.
replace xε with yε by apply pi; reflexivity.
Qed.

Lemma pEl_eq_rev : forall ℙ A p (x y : @pEl ℙ A p) q α,
  x = y -> x.(pel_elt) q α = y.(pel_elt) q α.
Proof.
intros.
destruct H; reflexivity.
Qed.

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

Definition of_psh {ℙ} (A : psh ℙ) : pfs ℙ.
Proof.
unshelve econstructor.
+ refine A.
+ refine (fun p x => forall q (α : ℙ q p), x q α = θ A α (x p (id p))).
Defined.

(** simple inlining of compatible (to_psh _) *)
Definition __compatible {ℙ : cat} (A : pfs ℙ) (J : site ℙ) {p : ℙ} (f : ste_fam J p)
    (s : forall i : ste_idx J p f, to_psh A (ste_obj J p f i)) :=
  forall (i₁ i₂ : ste_idx J p f) (q : ℙ) (α₁ : ℙ q (ste_obj J p f i₁))
    (α₂ : ℙ q (ste_obj J p f i₂)),
  α₁ ∘ ste_hom J p f i₁ = α₂ ∘ ste_hom J p f i₂ ->
  lift_pEl α₁ (s i₁) = lift_pEl α₂ (s i₂).

(** simple inlining of isSheaf (to_psh _) *)
Record __isSheaf (ℙ : cat) (A : pfs ℙ) (J : site ℙ) : Type := __Build_isSheaf
  { __shf_elt : forall (p : ℙ) (f : ste_fam J p)
                (s : forall i : ste_idx J p f, pEl A (ste_obj J p f i)),
              __compatible A J f s -> pEl A p;
    __shf_spc : forall (p : ℙ) (f : ste_fam J p)
                (s : forall i : ste_idx J p f, pEl A (ste_obj J p f i))
                (sc : __compatible A J f s) (i : ste_idx J p f),
              lift_pEl (ste_hom J p f i) (__shf_elt p f s sc) = s i;
    __shf_unq : forall (p : ℙ) (f : ste_fam J p)
                (s : forall x : ste_idx J p f, pEl A (ste_obj J p f x))
                (sc : __compatible A J f s) (x : pEl A p),
              (forall i : ste_idx J p f, lift_pEl (ste_hom J p f i) x = s i) ->
              x = __shf_elt p f s sc }.

Definition pfs_compatible {ℙ : cat} (A : pfs ℙ) (J : site ℙ)
  {p} (f : ste_fam J p)
  (s : forall (i : ste_idx J p f) q (α : ℙ q (ste_obj J p f i)), A q)
  (sε : forall (i : ste_idx J p f) q (α : ℙ q (ste_obj J p f i)),
      A.(pfs_rlz) q (fun r β => s i _ (β ∘ α)))
  :=
  forall (i₁ i₂ : ste_idx J p f) q
      (α₁ : ℙ q (ste_obj J p f i₁))
      (α₂ : ℙ q (ste_obj J p f i₂)),
      α₁ ∘ ste_hom J p f i₁ = α₂ ∘ ste_hom J p f i₂ ->
      s i₁ q α₁ = s i₂ q α₂.

Record isFascist {ℙ : cat} (A : pfs ℙ) (J : site ℙ) := {
  fsc_elt : forall (p : ℙ) (f : ste_fam J p) s sε (sc : @pfs_compatible _ A J p f s sε) q (α : ℙ q p), A q;
  fsc_rlz : forall (p : ℙ) (f : ste_fam J p) s sε (sc : @pfs_compatible _ A J p f s sε),
    forall q (α : ℙ q p), A.(pfs_rlz) q (fun r β => fsc_elt p f s sε sc r (β ∘ α));
  fsc_spc : forall p f s sε sc (i : ste_idx J p f) q (α : ℙ q (ste_obj J p f i)),
    fsc_elt p f s sε sc q (α ∘ ste_hom J p f i) = s i q α;
  fsc_unq : forall p f s sε sc (x : pEl A p),
    (forall i q (α : ℙ q _),
      x.(pel_elt) q (α ∘ ste_hom J p f i) = s i q α) ->
    forall q (α : ℙ q p),
    x.(pel_elt) q α = fsc_elt p f s sε sc q α;
}.

Lemma isFascist_hProp : forall ℙ A J (f₁ f₂ : @isFascist ℙ A J), f₁ = f₂.
Proof.
intros ℙ A J [f₁ fε₁ s₁ u₁ ] [f₂ fε₂ s₂ u₂].
assert (rw : f₁ = f₂).
{
  apply funext; intros p; apply funext; intros f; apply funext; intros s; apply funext; intros sε; apply funext; intros Hs.
  refine (let x₁ := Build_pEl _ A _ (f₁ p f s sε Hs) (fε₁ p f s sε Hs) in _).
  apply funext; intros q; apply funext; intros α.
  rewrite <- (u₂ p f _ _ _ x₁ (s₁ _ _ _ _ _) q α).
  reflexivity.
}
destruct rw.
replace fε₂ with fε₁ by apply pi.
replace s₂ with s₁ by apply pi.
replace u₂ with u₁ by apply pi.
reflexivity.
Qed.

Lemma isFascist_Sheaf :
  forall ℙ (J : site ℙ) A, isFascist A J -> isSheaf (to_psh A) J.
Proof.
intros ℙ J A [f fε e u].
unshelve econstructor.
+ refine (fun p ff s Hs => _).
  unshelve econstructor.
  - unshelve refine (fun q α => f _ _ _ _ _ q α).
    { exact ff. }
    { refine (fun i => (s i).(pel_elt)). }
    { refine (fun i => (s i).(pel_rlz)). }
    { refine (fun i₁ i₂ r β₁ β₂ rw => _).
      specialize (Hs i₁ i₂ r β₁ β₂ rw).
      cbn in Hs.
      assert (rw' := pEl_eq_rev _ _ _ _ _ r (id _) Hs).
      replace β₁ with (id _ ∘ β₁) by apply cat_cmp_l.
      replace β₂ with (id _ ∘ β₂) by apply cat_cmp_l.
      apply (pEl_eq_rev _ _ _ _ _ r (id _) Hs).
    }
  - intros q α; cbn.
    apply fε.
+ intros p ff s sc i.
  apply pEl_eq; intros q α; cbn.
  apply e.
+ intros p ff s sc x Hx; cbn.
  apply pEl_eq; cbn; intros q α.
  apply u.
  intros i r β.
  specialize (Hx i).
  cbn in Hx.
  apply (pEl_eq_rev _ _ _ _ _ r β Hx).
Defined.

Lemma isSheaf_Fascist :
  forall ℙ (J : site ℙ) A, isSheaf A J -> isFascist (of_psh A) J.
Proof.
intros ℙ J A [e r u].
unshelve econstructor.
+ intros p f s sε sc q α.
  refine (θ A α _).
  unshelve refine (e _ _ (fun i => s i _ (id _ ∘ id _)) _).
  clear - sc; intros i₁ i₂ q α₁ α₂ e.
  specialize (sc i₁ i₂ q α₁ α₂ e).
  cbn in sε.
  rewrite <- !sε, !cat_cmp_r; apply sc.
+ intros p f s sε sc q α w β; cbn.
  rewrite <- psh_mon_cmp, cat_cmp_l.
  f_equal.
+ intros p f s sε sc i q α; cbn.
  rewrite psh_mon_cmp, r.
  rewrite <- sε, cat_cmp_r; reflexivity.
+ intros p f s sε sc [x xε] Hx q α; cbn.
  cbn in *.
  rewrite <- (cat_cmp_r _ _ _ α), xε, (cat_cmp_r _ _ _ α).
  rewrite cat_cmp_l; f_equal.
  apply u; intros i.
  rewrite <- Hx.
  rewrite !cat_cmp_l.
  rewrite <- (cat_cmp_l _ _ _ (id _)), <- xε, cat_cmp_r.
  reflexivity.
Defined.
