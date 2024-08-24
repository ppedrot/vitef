Inductive Box (A : Type) : SProp := box : A -> Box A.

Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
Axiom pirrel : forall (A : Prop) (x y : A), x = y.
Axiom unbox : forall (A : Prop), Box A -> A.

Set Primitive Projections.

Record sig (A : Type) (B : A -> Type) := pair {
  fst : A;
  snd : B fst;
}.

Arguments pair {_ _}.
Arguments fst {_ _}.
Arguments snd {_ _}.

Lemma sig_eq_intro : forall (A : Type) (B : A -> Type) (p q : sig A B) (e : fst p = fst q),
  eq_rect _ B (snd p) _ e = snd q -> p = q.
Proof.
intros.
destruct p as [x y], q as [x' y']; cbn in *.
destruct e; f_equal; assumption.
Qed.

Definition prod (A B : Type) := sig A (fun _ => B).

Axiom M : Type -> Type.
Axiom ret : forall {A : Type}, A -> M A.
Axiom bind : forall {A B : Type}, M A -> (A -> M B) -> M B.

Axiom bind_ret_l : forall A B (x : A) (f : A -> M B), bind (ret x) f = f x.
Axiom bind_ret_r : forall A (α : M A), bind α ret = α.
Axiom bind_assoc : forall A B C (α : M A) f g,
  @bind B C (@bind A B α f) g = bind α (fun x => bind (f x) g).

Axiom nul : forall A, M A.
Axiom add : forall {A}, M A -> M A -> M A.

Axiom add_id_l : forall A (α : M A), add (nul A) α = α.
Axiom add_id_r : forall A (α : M A), add α (nul A) = α.
Axiom add_assoc : forall A (α₁ α₂ α₃ : M A), add α₁ (add α₂ α₃) = add (add α₁ α₂) α₃.
Axiom add_comm : forall A (α₁ α₂ : M A), add α₁ α₂ = add α₂ α₁.

Axiom bind_nul : forall A B (f : A -> M B), bind (nul A) f = nul B.
Axiom bind_add : forall A B (α₁ α₂ : M A) (f : A -> M B), bind (add α₁ α₂) f = add (bind α₁ f) (bind α₂ f).

Axiom bind_nul_rev : forall A B (α : M A), bind α (fun _ => nul B) = nul B.
Axiom bind_add_rev : forall A B (α : M A) (f g : A -> M B), bind α (fun x => add (f x) (g x)) = add (bind α f) (bind α g).

Definition map {A B} (f : A -> B) (α : M A) : M B := bind α (fun x => ret (f x)).

Lemma map_ret : forall A B (f : A -> B) (x : A), map f (ret x) = ret (f x).
Proof.
intros; unfold map.
now rewrite bind_ret_l.
Qed.

Lemma map_map : forall A B C (f : A -> B) (g : B -> C) (α : M A),
  map g (map f α) = map (fun x => g (f x)) α.
Proof.
intros; unfold map.
rewrite bind_assoc; f_equal.
apply funext; intros x; now rewrite bind_ret_l.
Qed.

Lemma map_bind : forall A B C (f : A -> M B) (g : B -> C) (α : M A),
  map g (bind α f) = bind α (fun x => map g (f x)).
Proof.
intros; unfold map.
now rewrite bind_assoc.
Qed.

Lemma map_nul : forall A B (f : A -> B), map f (nul _) = (nul _).
Proof.
intros; apply bind_nul.
Qed.

Lemma map_add : forall A B (f : A -> B) (α₁ α₂ : M A), map f (add α₁ α₂) = add (map f α₁) (map f α₂).
Proof.
intros; apply bind_add.
Qed.

Record isAlg (A : Type) (hA : M A -> A) (nulA : A) (addA : A -> A -> A) := {
  alg_ret : forall x, hA (ret x) = x;
  alg_bnd : forall (x : M (M A)), hA (map hA x) = hA (bind x (fun x => x));
  alg_id_l : forall x, addA nulA x = x;
  alg_id_r : forall x, addA x nulA = x;
  alg_assoc : forall x y z, addA x (addA y z) = addA (addA x y) z;
  alg_comm : forall x y, addA x y = addA y x;
  alg_run_nul : hA (nul _) = nulA;
  alg_run_add : forall x y, hA (add x y) = addA (hA x) (hA y);
}.

Class Alg (A : Type) := {
  alg_fun : M A -> A;
  alg_nul : A;
  alg_add : A -> A -> A;
  alg_spc : Box (isAlg A alg_fun alg_nul alg_add);
}.

Arguments alg_fun {A _}.
Arguments alg_nul {A _}.
Arguments alg_add {A _}.

Notation "'ε'" := (@alg_fun _ _).
Notation "∅" := (@alg_nul _ _).
Notation "x ⊕ y" := (@alg_add _ _ x y) (at level 35).

Lemma Alg_ret : forall {A} {algA : Alg A} (x : A), ε (ret x) = x.
Proof.
intros; eapply alg_ret, unbox, algA.
Qed.

Lemma Alg_bind₀ : forall {A} {algA : Alg A} (α : M (M A)), ε (map ε α) = ε (bind α (fun x => x)).
Proof.
intros; eapply alg_bnd, unbox, algA.
Qed.

Lemma Alg_bind : forall {A B} {algB : Alg B} (α : M A) (f : A -> M B),
  ε (bind α f) = ε (bind α (fun x => ret (ε (f x)))).
Proof.
intros.
transitivity (ε (bind (map f α) (fun x => x))).
{ unfold map; rewrite bind_assoc; do 2 f_equal.
  apply funext; intros x; now rewrite bind_ret_l. }
rewrite <- Alg_bind₀; f_equal.
now rewrite map_map.
Qed.

Lemma Alg_id_l : forall {A} {algA : Alg A} (x : A), ∅ ⊕ x = x.
Proof.
intros; eapply alg_id_l, unbox, algA.
Qed.

Lemma Alg_id_r : forall {A} {algA : Alg A} (x : A), x ⊕ ∅ = x.
Proof.
intros; eapply alg_id_r, unbox, algA.
Qed.

Lemma Alg_assoc : forall {A} {algA : Alg A} (x y z : A), x ⊕ (y ⊕ z) = (x ⊕ y) ⊕ z.
Proof.
intros; eapply alg_assoc, unbox, algA.
Qed.

Lemma Alg_comm : forall {A} {algA : Alg A} (x y : A), x ⊕ y = y ⊕ x.
Proof.
intros; eapply alg_comm, unbox, algA.
Qed.

Lemma Alg_run_nul : forall {A} {algA : Alg A}, ε (nul _) = ∅.
Proof.
intros; eapply alg_run_nul, unbox, algA.
Qed.

Lemma Alg_run_add : forall {A} {algA : Alg A} (α₁ α₂ : M A), ε (add α₁ α₂) = (ε α₁) ⊕ (ε α₂).
Proof.
intros; eapply alg_run_add, unbox, algA.
Qed.

Instance Alg_M {A} : Alg (M A).
Proof.
unshelve econstructor.
+ refine (fun α => bind α (fun x => x)).
+ refine (nul _).
+ refine (add).
+ do 2 constructor.
  - intros α; now rewrite bind_ret_l.
  - intros α; unfold map.
    rewrite !bind_assoc; f_equal; apply funext; intros β.
    now rewrite bind_ret_l.
  - intros; apply add_id_l.
  - intros; apply add_id_r.
  - intros; apply add_assoc.
  - intros; apply add_comm.
  - now rewrite bind_nul.
  - intros; now rewrite bind_add.
Defined.

Instance Alg_prod {A B} : Alg A -> Alg B -> Alg (prod A B).
Proof.
intros hA hB.
unshelve econstructor.
+ refine (fun α => pair (hA.(alg_fun) (map fst α)) (hB.(alg_fun) (map (@snd _ (fun _ => B)) α))).
+ refine (pair ∅ ∅).
+ refine (fun p q => pair (p.(fst) ⊕ q.(fst)) (p.(snd) ⊕ q.(snd))).
+ do 2 constructor.
  - intros [x y]; cbn; f_equal; now rewrite map_ret, Alg_ret.
  - intros α; f_equal; rewrite map_map; cbn;
    rewrite <- map_map with (g := ε), Alg_bind₀;
    f_equal; unfold map; rewrite !bind_assoc; f_equal;
    apply funext; intros β; now rewrite bind_ret_l.
  - intros [x y]; cbn; f_equal; apply Alg_id_l.
  - intros [x y]; cbn; f_equal; apply Alg_id_r.
  - intros [x y] [x' y'] [x'' y'']; cbn; f_equal; apply Alg_assoc.
  - intros [x y] [x' y']; cbn; f_equal; apply Alg_comm.
  - f_equal; now rewrite map_nul, Alg_run_nul.
  - intros; f_equal; cbn; now rewrite map_add, Alg_run_add.
Defined.

Definition Mlet {A B} {algB : Alg B} (α : M A) (f : A -> B) : B := ε (map f α).

Lemma Mlet_ret : forall {A B} {algB : Alg B} (x : A) (f : A -> B), Mlet (ret x) f = f x.
Proof.
intros; unfold Mlet, map.
now rewrite bind_ret_l, Alg_ret.
Qed.

Lemma Mlet_assoc : forall {A B C} {algC : Alg C} (α : M A) (f : A -> M B) (g : B -> C),
  Mlet (bind α f) g = Mlet α (fun x => Mlet (f x) g).
Proof.
intros; unfold Mlet; cbn.
rewrite <- map_map with (g := ε).
rewrite Alg_bind₀.
f_equal.
rewrite map_bind; unfold map.
rewrite !bind_assoc.
f_equal.
apply funext; intros x.
now rewrite !bind_ret_l.
Qed.

Lemma Mlet_map : forall {A B C} {algC : Alg C} (α : M A) (f : A -> B) (g : B -> C),
  (Mlet (map f α) g) = Mlet α (fun x => g (f x)).
Proof.
intros; unfold Mlet.
now rewrite map_map.
Qed.

Lemma Mlet_nul : forall {A B} {algB : Alg B} (α : M A), Mlet α (fun x => ∅) = @alg_nul B algB.
Proof.
intros; unfold Mlet, map.
set (e := ∅) at 1; rewrite <- Alg_run_nul; unfold e; clear e.
rewrite <- bind_nul_rev with (α := α).
symmetry; rewrite Alg_bind; do 2 f_equal.
apply funext; intros x.
now rewrite Alg_run_nul.
Qed.

Lemma Mlet_add : forall {A B} {algB : Alg B} (α : M A) (f g : A -> B),
  Mlet α (fun x => (f x) ⊕ (g x)) = (Mlet α f) ⊕ (Mlet α g).
Proof.
intros; symmetry; unfold Mlet.
rewrite <- Alg_run_add.
unfold map. rewrite <- bind_add_rev, Alg_bind; do 2 f_equal.
apply funext; intros x.
now rewrite Alg_run_add, !Alg_ret.
Qed.

(** The Dialectica CwF *)

Record Ctx := {
  ctx_wit : Type;
  ctx_ctr : forall (γ : ctx_wit), Type;
  ctx_alg :: forall (γ : ctx_wit), Alg (ctx_ctr γ);
}.

Record isSub {Γ Δ : Ctx}
  (fwd : forall (γ : ctx_wit Γ), ctx_wit Δ)
  (bwd : forall (γ : ctx_wit Γ), ctx_ctr Δ (fwd γ) -> ctx_ctr Γ γ) := {
  sub_alg : forall γ π, bwd γ (ε π) = ε (map (bwd γ) π);
}.

Record Sub (Γ Δ : Ctx) := {
  sub_fwd : forall (γ : ctx_wit Γ), ctx_wit Δ;
  sub_bwd : forall (γ : ctx_wit Γ), ctx_ctr Δ (sub_fwd γ) -> ctx_ctr Γ γ;
  sub_spc : Box (isSub sub_fwd sub_bwd);
}.

Arguments sub_fwd {Γ Δ}.
Arguments sub_bwd {Γ Δ}.

Lemma Sub_alg : forall {Γ Δ} (σ : Sub Γ Δ) (γ : ctx_wit Γ) π, sub_bwd σ γ (ε π) = ε (map (sub_bwd σ γ) π).
Proof.
intros; apply sub_alg, unbox, σ.
Qed.

Lemma Sub_nul : forall {Γ Δ} (σ : Sub Γ Δ) (γ : ctx_wit Γ), sub_bwd σ γ ∅ = ∅.
Proof.
intros.
now rewrite <- Alg_run_nul, Sub_alg, !map_nul, Alg_run_nul.
Qed.

Lemma Sub_add : forall {Γ Δ} (σ : Sub Γ Δ) (γ : ctx_wit Γ) π₁ π₂, sub_bwd σ γ (π₁ ⊕ π₂) = sub_bwd σ γ π₁ ⊕ sub_bwd σ γ π₂.
Proof.
intros.
rewrite <- (Alg_ret π₁), <- (Alg_ret π₂).
rewrite <- Alg_run_add, Sub_alg, !map_add, !map_ret.
now rewrite Alg_run_add, !Alg_ret.
Qed.

Definition idn (Γ : Ctx) : Sub Γ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ => γ).
+ refine (fun γ π => π).
+ do 2 constructor.
  intros; unfold map; now rewrite bind_ret_r.
Defined.

Definition cmp {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Ξ) : Sub Γ Ξ.
Proof.
unshelve econstructor.
+ refine (fun γ => τ.(sub_fwd) (σ.(sub_fwd) γ)).
+ refine (fun γ π => σ.(sub_bwd) γ (τ.(sub_bwd) _ π)).
+ do 2 constructor.
  intros; now rewrite !Sub_alg, map_map.
Defined.

Record Typ (Γ : Ctx) := {
  typ_wit : forall (γ : Γ.(ctx_wit)), Type;
  typ_ctr : forall (γ : Γ.(ctx_wit)) (x : typ_wit γ), Type;
}.

Arguments typ_wit {Γ}.
Arguments typ_ctr {Γ}.

Definition typ_sub {Γ Δ : Ctx} (A : Typ Γ) (σ : Sub Δ Γ) : Typ Δ.
Proof.
unshelve econstructor.
+ refine (fun γ => A.(typ_wit) (σ.(sub_fwd) γ)).
+ refine (fun γ x => A.(typ_ctr) (σ.(sub_fwd) γ) x).
Defined.

Lemma typ_sub_idn : forall Γ A, typ_sub A (idn Γ) = A.
Proof.
reflexivity.
Defined.

Lemma typ_sub_cmp : forall Γ Δ Ξ A σ τ, typ_sub A (@cmp Γ Δ Ξ σ τ) = typ_sub (typ_sub A τ) σ.
Proof.
reflexivity.
Defined.

Record Trm (Γ : Ctx) (A : Typ Γ) := {
  trm_fwd : forall (γ : Γ.(ctx_wit)), typ_wit A γ;
  trm_bwd : forall (γ : Γ.(ctx_wit)), typ_ctr A γ (trm_fwd γ) -> ctx_ctr Γ γ;
}.

Arguments trm_fwd {_ _}.
Arguments trm_bwd {_ _}.

Lemma trm_eq_intro : forall Γ A (t u : Trm Γ A) (e : forall γ, t.(trm_fwd) γ = u.(trm_fwd) γ),
  (forall γ π, t.(trm_bwd) γ π = u.(trm_bwd) γ (eq_rect _ (typ_ctr A γ) π _ (e γ))) ->
  t = u.
Proof.
intros.
destruct t as [tf tb], u as [uf ub]; cbn in *.
assert (e₀ := funext _ _ _ _ e); destruct e₀; f_equal.
apply funext; intros γ; apply funext; intros π.
specialize (H γ π).
replace (e γ) with (@eq_refl _ (tf γ)) in H by apply pirrel.
apply H.
Qed.

Definition trm_sub {Γ Δ : Ctx} {A : Typ Γ} (x : Trm Γ A) (σ : Sub Δ Γ) : Trm Δ (typ_sub A σ).
Proof.
unshelve econstructor.
+ refine (fun γ => x.(trm_fwd) _).
+ refine (fun γ π => σ.(sub_bwd) _ (x.(trm_bwd) _ π)).
Defined.

Lemma trm_sub_idn : forall Γ (A : Typ Γ) (x : Trm Γ A), trm_sub x (idn Γ) = x.
Proof.
reflexivity.
Qed.

Lemma trm_sub_cmp : forall Γ Δ Ξ (A : Typ Ξ) (x : Trm Ξ A) (σ : Sub Γ Δ) (τ : Sub Δ Ξ),
  trm_sub x (cmp σ τ) = trm_sub (trm_sub x τ) σ.
Proof.
reflexivity.
Qed.

(** Context extension *)

Definition ext (Γ : Ctx) (A : Typ Γ) : Ctx.
Proof.
unshelve econstructor.
+ refine (sig Γ.(ctx_wit) (fun γ => A.(typ_wit) γ)).
+ refine (fun γ => prod (Γ.(ctx_ctr) γ.(fst)) (M (A.(typ_ctr) γ.(fst) γ.(snd)))).
+ cbn; intros γ.
  apply Alg_prod.
  - apply ctx_alg.
  - apply Alg_M.
Defined.

Definition wkn {Γ Δ} (A : Typ Γ) (σ : Sub Γ Δ) : Sub (ext Γ A) Δ.
Proof.
unshelve econstructor.
+ refine (fun γ => σ.(sub_fwd) (γ.(fst))).
+ refine (fun γ π => pair (σ.(sub_bwd) _ π) ∅).
+ do 2 constructor.
  intros [γ x] π; cbn.
  rewrite !Sub_alg, !map_map; cbn; f_equal.
  unfold map; rewrite bind_assoc; cbn.
  symmetry; etransitivity; [|apply bind_nul_rev with (α := π)].
  f_equal; apply funext; intros ρ.
  now rewrite bind_ret_l.
Defined.

Lemma wkn_cmp : forall Γ Δ Ξ A (σ : Sub Γ Δ) (τ : Sub Δ Ξ),
  wkn A (cmp σ τ) = cmp (wkn A σ) τ.
Proof.
reflexivity.
Qed.

Lemma lft {Γ Δ} (A : Typ Δ) (σ : Sub Γ Δ) : Sub (ext Γ (typ_sub A σ)) (ext Δ A).
Proof.
unshelve econstructor.
+ refine (fun γ => pair (sub_fwd σ γ.(fst)) γ.(snd)).
+ refine (fun γ π => pair (sub_bwd σ γ.(fst) π.(fst)) π.(snd)).
+ do 2 constructor.
  intros [γ x] π; cbn.
  rewrite !Sub_alg, !map_map; reflexivity.
Defined.

Definition rel0 {Γ : Ctx} {A : Typ Γ} : Trm (ext Γ A) (typ_sub A (wkn A (idn _))).
Proof.
unshelve econstructor.
+ refine (fun γ => γ.(snd)).
+ refine (fun γ π => pair ∅ (ret π)).
Defined.

Definition cns {Γ Δ} {A : Typ Γ} (σ : Sub Δ Γ) (x : Trm Δ (typ_sub A σ)) : Sub Δ (ext Γ A).
Proof.
unshelve econstructor.
+ refine (fun δ => pair (σ.(sub_fwd) δ) (x.(trm_fwd) δ)).
+ cbn; refine (fun δ π => _).
  refine ((σ.(sub_bwd) _ π.(fst)) ⊕ (Mlet π.(snd) (fun ρ => x.(trm_bwd) δ ρ))).
+ do 2 constructor; intros δ π; cbn.
  match goal with [ |- _ = ε (map ?h π) ] => change (ε (map h π)) with (Mlet π h) end.
  rewrite Sub_alg.
  match goal with [ |- ε (map ?h ?π) ⊕ _ = _ ] => change (ε (map h π)) with (Mlet π h) end.
  rewrite Mlet_assoc, !Mlet_map, Mlet_add; reflexivity.
Defined.

Lemma cns_rel0 : forall Γ Δ A (σ : Sub Δ Γ) x, trm_sub (@rel0 _ A) (cns σ x) = x.
Proof.
intros Γ Δ A σ [xf xb].
unfold trm_sub; f_equal.
apply funext; intros δ; apply funext; intros π; cbn.
now rewrite Sub_nul, Alg_id_l, Mlet_ret.
Qed.

(** Product type and term formers *)

Definition Π {Γ : Ctx} (A : Typ Γ) (B : Typ (ext Γ A)) : Typ Γ.
Proof.
unshelve econstructor.
+ unshelve refine (fun γ =>
    forall (x : typ_wit A γ),
      sig (typ_wit B (pair γ x)) (fun y => typ_ctr B (pair γ x) y -> M (typ_ctr A γ x))
  ).
+ unshelve refine (fun γ f =>
    sig (typ_wit A γ) (fun x => typ_ctr B (pair γ x) (f x).(fst))
  ).
Defined.

Definition lam {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm (ext Γ A) B) : Trm Γ (Π A B).
Proof.
unshelve econstructor.
+ unshelve refine (fun γ x => pair _ _).
  - refine (t.(trm_fwd) (pair γ x)).
  - refine (fun π => (t.(trm_bwd) (pair γ x) π).(snd)).
+ refine (fun γ π => (t.(trm_bwd) (pair γ π.(fst)) π.(snd)).(fst)).
Defined.

Definition app {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm Γ (Π A B)) (u : Trm Γ A) :
  Trm Γ (typ_sub B (cns (idn Γ) u)).
Proof.
unshelve econstructor.
+ refine (fun γ => (t.(trm_fwd) γ (u.(trm_fwd) γ)).(fst)).
+ refine (fun γ π => _ ⊕ _).
  - refine (t.(trm_bwd) γ (pair (u.(trm_fwd) γ) π)).
  - refine (Mlet ((t.(trm_fwd) γ (u.(trm_fwd) γ)).(snd) π) (u.(trm_bwd) γ)).
Defined.

Lemma Π_sub : forall {Γ Δ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (σ : Sub Δ Γ),
  typ_sub (Π A B) σ = Π (typ_sub A σ) (typ_sub B (lft A σ)).
Proof.
reflexivity.
Qed.

Lemma lam_sub : forall {Γ Δ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm (ext Γ A) B) (σ : Sub Δ Γ),
  trm_sub (lam t) σ = lam (trm_sub t (lft _ σ)).
Proof.
reflexivity.
Qed.

Lemma app_sub : forall {Γ Δ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)}
  (t : Trm Γ (Π A B)) (u : Trm Γ A) (σ : Sub Δ Γ),
  trm_sub (app t u) σ = @app _ (typ_sub A σ) (typ_sub B (lft A σ)) (trm_sub t σ) (trm_sub u σ).
Proof.
intros; unfold trm_sub, app; cbn; f_equal.
apply funext; intros γ; apply funext; intros π; cbn.
rewrite Sub_add; f_equal.
unfold Mlet; rewrite Sub_alg, !map_map.
reflexivity.
Qed.

Lemma lam_app_beta : forall {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)}
  (t : Trm (ext Γ A) B) (u : Trm Γ A), app (lam t) u = trm_sub t (cns (idn Γ) u).
Proof.
reflexivity.
Qed.

Lemma trm_Π_eq_intro : forall {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t u : Trm Γ (Π A B))
  (ef : forall γ x, (t.(trm_fwd) γ x).(fst) = (u.(trm_fwd) γ x).(fst)),
  (forall γ x π, (t.(trm_fwd) γ x).(snd) π = (u.(trm_fwd) γ x).(snd) (eq_rect _ _ π _ (ef γ x))) ->
  (forall γ x π, t.(trm_bwd) γ (pair x π) = u.(trm_bwd) γ (pair x (eq_rect _ (typ_ctr B (pair γ x)) π _ (ef γ x)))) ->
  t = u.
Proof.
intros * eb er.
destruct t as [tf tb], u as [uf ub].
pose (tff := fun γ x => (tf γ x).(fst)).
pose (tfb := fun γ x => (tf γ x).(snd)).
change tf with (fun γ x => pair (tff γ x) (tfb γ x)) in tb, ef, eb, er |- *.
clearbody tfb.
change (forall γ x, typ_ctr B {| fst := γ; snd := x |} (tff γ x) -> M (typ_ctr A γ x)) in tfb.
clearbody tff; clear tf.
pose (uff := fun γ x => (uf γ x).(fst)).
pose (ufb := fun γ x => (uf γ x).(snd)).
change uf with (fun γ x => pair (uff γ x) (ufb γ x)) in ub, ef, eb, er |- *.
clearbody ufb.
change (forall γ x, typ_ctr B {| fst := γ; snd := x |} (uff γ x) -> M (typ_ctr A γ x)) in ufb.
clearbody uff; clear uf.
cbn in *.
unshelve eapply trm_eq_intro.
+ cbn; intros γ.
  assert (e : tff = uff).
  { abstract (do 2 (apply funext; intro); apply ef). }
  destruct e.
  assert (e : tfb = ufb).
  { clear - eb. apply funext; intros γ; apply funext; intros x; apply funext; intros π.
    specialize (eb γ x π).
    rewrite eb; f_equal.
    replace (ef γ x) with (@eq_refl _ (tff γ x)) by apply pirrel.
    reflexivity. }
  now destruct e.
+ cbn; intros γ [x π]; cbn in *.
  match goal with [ |- context [ eq_rect ?A ?P ?u ?y ?p ] ] => set (e := p); clearbody e end.
  etransitivity; [apply er|].
  f_equal.
  unshelve eapply sig_eq_intro; cbn.
  - destruct e; reflexivity.
  - cbn.
    assert (eff : tff = uff).
    { do 2 (apply funext; intro); apply ef. }
    destruct eff; cbn.
    assert (efb : tfb = ufb).
    { clear - eb. apply funext; intros γ; apply funext; intros x; apply funext; intros π.
      specialize (eb γ x π).
      rewrite eb; f_equal.
      replace (ef γ x) with (@eq_refl _ (tff γ x)) by apply pirrel.
      reflexivity. }
    destruct efb.
    repeat match goal with [ |- context [ eq_rect ?A ?P ?u ?y ?p ] ] =>
      set (e' := p); clearbody e'; assert (H : e' = eq_refl) by apply pirrel; rewrite H; clear e' H; cbn
    end.
    reflexivity.
Qed.

Lemma lam_eta_fwd : forall {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm Γ (Π A B)) γ,
  trm_fwd (lam (@app (ext Γ A) (typ_sub A (wkn _ (idn _))) (typ_sub B (lft A _)) (trm_sub t (wkn A (idn Γ))) rel0)) γ =
  trm_fwd t γ.
Proof.
intros; cbn.
apply funext; intros x; cbn.
apply (f_equal (pair (fst (trm_fwd t γ x)))).
apply funext; intros π; cbn in *.
rewrite add_id_l, map_map; cbn.
unfold map; rewrite bind_assoc.
etransitivity; [|apply bind_ret_r].
f_equal; apply funext; intros ρ.
now rewrite bind_ret_l.
Qed.

Lemma lam_eta : forall {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm Γ (Π A B)),
  lam (@app (ext Γ A) (typ_sub A (wkn _ (idn _))) (typ_sub B (lft A _)) (trm_sub t (wkn A (idn Γ))) rel0) = t.
Proof.
intros.
unshelve eapply trm_Π_eq_intro.
+ reflexivity.
+ cbn; intros γ x π.
  rewrite add_id_l; rewrite map_map; unfold map; rewrite bind_assoc.
  etransitivity; [|apply bind_ret_r].
  f_equal; apply funext; intros ρ.
  now rewrite bind_ret_l.
+ cbn; intros γ x π.
  rewrite map_map; cbn.
  match goal with [ |- _ ⊕ (ε (map ?f ?t)) = _ ] => change (ε (map ?f ?t)) with (Mlet t f) end.
  now rewrite Mlet_nul, Alg_id_r.
Qed.
