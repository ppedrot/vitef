Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive True : SProp := I.
Inductive False : SProp :=.
Inductive and (A : SProp) (B : SProp) : SProp := conj : A -> B -> and A B.

Axiom F : False.
Ltac admit := case F.

Set Definitional UIP.

Inductive eqn (A : Type) (x : A) : A -> SProp := refl : eqn A x x.

Unset Definitional UIP.

Arguments eqn {_}.
Arguments eqn_rect {_ _} _ _ {_}.

Definition rew {A} (P : A -> SProp) {x y : A} (e : eqn x y) (p : P x) : P y :=
  match e in eqn _ z return P z with refl _ _ => p end.

Definition transp {A} (P : A -> Type) {x y : A} (e : eqn x y) (p : P x) : P y.
Proof.
refine (match e in eqn _ z return P z with refl _ _ => p end).
Defined.

Record sig (A : Type) (B : A -> Type) := pair { fst : A; snd : B fst }.

Arguments fst {_ _}.
Arguments snd {_ _}.

Record exist (A : Type) (B : A -> SProp) := pack { val : A; spc : B val }.

Arguments val {_ _}.
Arguments spc {_ _}.

Axiom ℙ : Set.
Axiom le0 : ℙ -> ℙ -> Set.

Definition le (p q : ℙ) := forall r, le0 q r -> le0 p r.

Notation "p ≤ q" := (le p q) (at level 70).
Notation "α ∘ β" := (fun (r : ℙ) (γ : le0 _ r) => α r (β r γ)) (at level 50).
Notation "!" := (fun (r : ℙ) (γ : le0 _ r) => γ).
Notation "α · t" := (fun (q : ℙ) (β : q ≤ _) => t q (β ∘ α)) (at level 50).

Record Ctx := {
  ctx_typ : forall p, Type;
  ctx_rel : forall (p : ℙ), (forall q (α : q ≤ p), ctx_typ q) -> SProp;
}.

Coercion ctx_typ : Ctx >-> Funclass.
Arguments ctx_rel _ {_}.

Record Sub (Γ Δ : Ctx) := {
  sub_fun : forall p
    (γ : forall q (α : q ≤ p), Γ q)
    (γε : forall q (α : q ≤ p), ctx_rel Γ (α · γ)),
    Δ p;
  sub_rel : forall p
    (γ : forall q (α : q ≤ p), Γ q)
    (γε : forall q (α : q ≤ p), ctx_rel Γ (α · γ)),
    ctx_rel Δ (fun q α => sub_fun q (α · γ) (α · γε));
}.

Coercion sub_fun : Sub >-> Funclass.

Arguments sub_fun {_ _}.
Arguments sub_rel {_ _}.

Definition Idn {Γ : Ctx} : Sub Γ Γ.
Proof.
unshelve econstructor.
+ unshelve refine (fun p γ γε => γ p !).
+ unshelve refine (fun p γ γε => γε p !).
Defined.

Definition Cmp {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (ρ : Sub Δ Ξ) : Sub Γ Ξ.
Proof.
unshelve econstructor.
+ unshelve refine (fun p γ γε => ρ _ _ _).
  unshelve refine (fun q α => σ _ (α · γ) (fun r β => γε _ (β ∘ α))).
  unshelve refine (fun q α => σ.(sub_rel) _ (α · γ) (α · γε)).
+ unshelve refine (fun p γ γε =>
  ρ.(sub_rel) _
    (fun q α => σ _ (α · γ) (fun r β => γε _ (β ∘ α)))
    (fun q α => σ.(sub_rel) _ (α · γ) (α · γε))
).
Defined.

Lemma Idn_Cmp : forall {Γ Δ} (σ : Sub Γ Δ), Cmp Idn σ = σ.
Proof.
reflexivity.
Qed.

Lemma Cmp_Idn : forall {Γ Δ} (σ : Sub Γ Δ), Cmp σ Idn = σ.
Proof.
reflexivity.
Qed.

Lemma Cmp_Cmp : forall {Γ Δ Ξ Ω} (σ : Sub Γ Δ) (ρ : Sub Δ Ξ) (θ : Sub Ξ Ω),
  Cmp (Cmp σ ρ) θ = Cmp σ (Cmp ρ θ).
Proof.
reflexivity.
Qed.

Record Typ (Γ : Ctx) := {
  typ_typ : forall p
    (γ : forall q (α : q ≤ p), Γ q)
    (γε : forall q (α : q ≤ p), ctx_rel Γ (α · γ)),
    Type;
  typ_rel : forall p
    (γ : forall q (α : q ≤ p), Γ q)
    (γε : forall q (α : q ≤ p), ctx_rel Γ (α · γ))
    (x : forall q (α : q ≤ p), typ_typ q (α · γ) (α · γε)), SProp;
}.

Coercion typ_typ : Typ >-> Funclass.
Arguments typ_rel {_} _ {_ _ _}.

Definition Typ_subs {Γ Δ : Ctx} (σ : Sub Δ Γ) (A : Typ Γ) : Typ Δ.
Proof.
unshelve econstructor.
+ unshelve refine (fun p δ δε => A p (fun q α => σ q (α · δ) (α · δε)) _).
  unshelve refine (fun q α => σ.(sub_rel) q (α · δ) (α · δε)).
+ unshelve refine (
  fun p δ δε x => @typ_rel _ A _
    (fun q α => σ q (α · δ) (α · δε))
    (fun q α => σ.(sub_rel) q (α · δ) (α · δε)) x).
Defined.

Record Trm (Γ : Ctx) (A : Typ Γ) := {
  trm_elt : forall p
    (γ : forall q (α : q ≤ p), Γ q)
    (γε : forall q (α : q ≤ p), ctx_rel Γ (α · γ)),
    A p γ γε;
  trm_rel : forall p
    (γ : forall q (α : q ≤ p), Γ q)
    (γε : forall q (α : q ≤ p), ctx_rel Γ (α · γ)),
    @typ_rel Γ A p γ γε (fun q (α : q ≤ p) => trm_elt q (α · γ) (α · γε))
}.

Arguments trm_elt {_ _}.
Arguments trm_rel {_ _}.

Definition Trm_subs {Γ Δ : Ctx} (σ : Sub Δ Γ) {A : Typ Γ}
  (t : Trm Γ A) : Trm Δ (Typ_subs σ A).
Proof.
unshelve econstructor.
+ simpl; refine (fun p γ γε => _).
  refine (t.(trm_elt) _ _ (fun q α => sub_rel σ q (α · γ) (α · γε))).
+ simpl; refine (fun p γ γε => _).
  refine (t.(trm_rel) _ _ (fun q α => sub_rel σ q (α · γ) (α · γε))).
Defined.

Definition Nil : Ctx.
Proof.
unshelve econstructor.
+ refine (fun _ => unit).
+ refine (fun _ _ => True).
Defined.

Record Ext_typ (Γ : Ctx) (A : Typ Γ) (p : ℙ) := {
  ext_typ_ctx : forall q (α : q ≤ p), Γ q;
  ext_typ_rel : forall q (α : q ≤ p), ctx_rel Γ (α · ext_typ_ctx);
  ext_typ_ext : A p ext_typ_ctx ext_typ_rel;
}.

Arguments ext_typ_ctx {_ _ _}.
Arguments ext_typ_rel {_ _ _}.
Arguments ext_typ_ext {_ _ _}.

Definition Build_Ext_typ₀ {Γ : Ctx} {A : Typ Γ} {p : ℙ}
  (γ : forall (q : ℙ) (α : q ≤ p), Γ q)
  (γε : forall (q : ℙ) (α : q ≤ p), ctx_rel Γ (α · γ))
  (x : forall (q : ℙ) (α : q ≤ p), A q (α · γ) (α · γε))
  (xε : forall (q : ℙ) (α : q ≤ p), @typ_rel Γ A q (α · γ) (α · γε) (α · x)) :
  forall q (α : q ≤ p), Ext_typ Γ A q :=
  fun q α => Build_Ext_typ _ _ _ (fun r β => γ r (β ∘ α)) (α · γε) (x q α).

Definition run {A : ℙ -> Type} {p : ℙ}
  (x : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), A r) :
  forall (q : ℙ) (α : q ≤ p), A q := fun q (α : q ≤ p) => x q α q !.

Definition ret {A : ℙ -> Type} {p : ℙ}
  (x : forall (q : ℙ) (α : q ≤ p), A q) :
  forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), A r :=
    fun q (α : q ≤ p) r (β : r ≤ q) => x r (β ∘ α).

Definition evl {A} {p} x := @ret A p (@run A p x).

Definition Fε {A : ℙ -> Type} {p : ℙ}
  (x : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), A r) :=
  eqn x (evl x).

Definition ΘF {A} {p : ℙ}
  (x : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), A r)
  (xε : @Fε A p x) {q} (α : q ≤ p) : @Fε A q (α · x).
Proof.
refine (match xε in eqn _ z return Fε (α · z) -> Fε (α · x) with refl _ _ => fun e => e end _).
reflexivity.
Defined.

Notation "α • xε" := (ΘF _ xε α)  (at level 50).

Definition Θ {Γ : Ctx} {p : ℙ}
  (γ : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), Γ r)
  (γε : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), ctx_rel Γ (β · (γ q α)))
  (γe : Fε γ) :
  forall (q : ℙ) (α : q ≤ p),
    ctx_rel Γ (fun  (r : ℙ) (β : r ≤ q) => γ r (β ∘ α) r !) :=
  rew (fun γ₀ => forall q (α : q ≤ p), ctx_rel Γ (α · (γ₀ p !))) γe (γε p !).

Definition F_rect {A : ℙ -> Type} {p : ℙ}
  (P : forall
    (x : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), A r)
    (xε : Fε x),
    Type
  )
  (u : forall
    (x : forall (q : ℙ) (α : q ≤ p), A q),
    P (ret x) (refl _ _)
  )
  (x : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), A r)
  (xε : Fε x) :
  P x xε.
Proof.
unshelve refine (
  eqn_rect (fun x₀ (e₀ : eqn (evl x) x₀) => P x₀ (rew Fε e₀ (refl _ _))) (u (run x))
  (rew (fun z => eqn z _) xε (refl _ _))
).
Defined.

Definition F_sind {A : ℙ -> Type} {p : ℙ}
  (P : forall
    (x : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), A r)
    (xε : Fε x),
    SProp
  )
  (u : forall
    (x : forall (q : ℙ) (α : q ≤ p), A q),
    P (ret x) (refl _ _)
  )
  (x : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), A r)
  (xε : Fε x) :
  P x xε.
Proof.
unshelve refine (
  eqn_sind _ _ (fun x₀ (e₀ : eqn (evl x) x₀) => P x₀ (rew Fε e₀ (refl _ _))) (u (run x))
  _ (rew (fun z => eqn z _) xε (refl _ _))
).
Defined.

Definition letΘ {Γ : Ctx} {A : Typ Γ} {p : ℙ}
  (γ : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), Γ r)
  (γε : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), ctx_rel Γ (β · (γ q α)))
  (γe : Fε γ)
  (x : forall q (α : q ≤ p), A q (γ q α) (γε q α)) :
  (forall (q : ℙ) (α : q ≤ p), A q (evl γ q α) (α · Θ _ γε γe)).
Proof.
refine (fun q (α : q ≤ p) =>
  eqn_rect
    (fun
      (γ₀ : forall r : ℙ, r ≤ q -> Γ r)
      (e₀ : eqn (γ q α) γ₀) =>
        A q γ₀ (rew (fun γ₀ => forall (r : ℙ) (β : r ≤ q), ctx_rel Γ (β · γ₀)) e₀ (γε q α))
  )
  (x q α)
  (rew (fun γ₀ => eqn _ (γ₀ q α)) γe (refl _ _))
).
(*
refine (fun q (α : q ≤ p) =>
  F_rect (fun γ₀ e₀ => forall γε, A q (γ₀ q α) (γε q α) -> A q (evl γ₀ q α) (α · Θ γ₀ γε e₀)) (fun γ γε x => x) γ γe γε (x q α)
).
*)
Defined.

Lemma letΘ_mono : forall Γ A p γ γε γe x q (α : q ≤ p),
  α · (@letΘ Γ A p γ γε γe x) = @letΘ Γ A q (α · γ) (α · γε) (α • γe) (α · x).
Proof.
reflexivity.
Qed.

Definition eqn_sym {A} {x y : A} (e : eqn x y) : eqn y x.
Proof.
destruct e; reflexivity.
Qed.

Definition eqn_trs {A} {x y z : A} (p : eqn x y) (q : eqn y z) : eqn x z.
Proof.
destruct p, q; reflexivity.
Qed.

Definition eqn_app {A B} (f : A -> B) {x y : A} (e : eqn x y) : eqn (f x) (f y).
Proof.
destruct e; reflexivity.
Qed.

Record Ext_rel (Γ : Ctx) (A : Typ Γ) (p : ℙ)
  (γ : forall q (β : q ≤ p) r (β : r ≤ q), Γ r)
  (γε : forall q (α : q ≤ p) r (β : r ≤ q), ctx_rel Γ (β · (γ q α)))
  (x : forall q (α : q ≤ p), A q (γ q α) (γε q α)) : SProp := {

  ext_rel_ctx : Fε γ;

  ext_rel_ext :
    forall q (α : q ≤ p),
    @typ_rel _ A q
      (fun r (β : r ≤ q) => (γ r (β ∘ α)) r !)
      (Θ _ (fun r β => (γε r (β ∘ α))) (α • ext_rel_ctx))
      (letΘ _ _ (α • ext_rel_ctx) (α · x))
}.

Arguments ext_rel_ctx {_ _ _ _ _ _}.
Arguments ext_rel_ext {_ _ _ _ _ _}.

Definition Ext (Γ : Ctx) (A : Typ Γ) : Ctx.
Proof.
unshelve econstructor.
+ refine (Ext_typ Γ A).
+ refine (fun p γ =>
  Ext_rel Γ A p
    (fun q α => (γ q α).(ext_typ_ctx))
    (fun q α => (γ q α).(ext_typ_rel))
    (fun q α => (γ q α).(ext_typ_ext))
).
Defined.

Definition Cns (Γ : Ctx) (A : Typ Γ) (t : Trm Γ A) : Sub Γ (Ext Γ A).
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => _).
  unshelve econstructor.
  - refine γ.
  - refine γε.
  - refine (t.(trm_elt) _ γ γε).
+ simpl; refine (fun p γ γε => _).
  unshelve econstructor; simpl; [reflexivity|].
  simpl. refine (fun q α => t.(trm_rel) _ _ _).
Defined.

Definition Wkn (Γ : Ctx) (A : Typ Γ) : Sub (Ext Γ A) Γ.
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => (γ p !).(ext_typ_ctx) p !).
+ simpl.
  intros p γ γε.
  refine (Θ _ _ ((γε p !).(ext_rel_ctx)) p !).
  refine (fun q α => (γ q α).(ext_typ_rel)).
Defined.

Definition Lft {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Typ Δ) :
  Sub (Ext Γ (Typ_subs σ A)) (Ext Δ A).
Proof.
unshelve econstructor.
+ unshelve refine (fun p γ γε => Build_Ext_typ _ _ _ _ _ _); simpl in *.
  - unshelve refine (fun q α => σ q (fun r (β : r ≤ q) => (γ r (β ∘ α)).(ext_typ_ctx) r !) _).
    refine (Θ _ (fun r β => (γ r (β ∘ α)).(ext_typ_rel)) ((γε q α).(ext_rel_ctx))).

  - refine (fun q α => σ.(sub_rel) q
      (fun r (β : r ≤ q) => (γ r (β ∘ α)).(ext_typ_ctx) r !)
      (rew (fun γ₀ => forall r (β : r ≤ q), ctx_rel Γ (β · (γ₀ q α))) ((γε p !).(ext_rel_ctx)) (γ q α).(ext_typ_rel))
    ).
  - refine (

      eqn_rect (fun γ₀ e₀ =>
      let e₁ := rew (fun γ₁ => forall (q : ℙ) (α : q ≤ p), ctx_rel Γ (α · γ₁)) e₀ (γ p !).(ext_typ_rel) in
      A p
        (fun (q : ℙ) (α : q ≤ p) =>
         σ q (α · γ₀)
           (α · e₁))
        (fun (q : ℙ) (α : q ≤ p) =>
         sub_rel σ q (α · γ₀)
           (α · e₁))
      ) ((γ p !).(ext_typ_ext)) (rew (fun γ₀ => eqn _ (γ₀ p !)) (ext_rel_ctx (γε p !)) (refl _ _))
    ).
+ simpl.
  refine (fun p γ γε => _).
  unshelve econstructor.
  - reflexivity.
  - refine (fun q α => _).
    refine ((γε q α).(ext_rel_ext) q !).
Defined.

Definition Var {Γ : Ctx} {A : Typ Γ} : Trm (Ext Γ A) (Typ_subs (Wkn Γ A) A).
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => _).
  refine (letΘ _ (fun q α => (γ q α).(ext_typ_rel)) ((γε p !).(ext_rel_ctx)) _ p !).
  refine (fun q α => (γ q α).(ext_typ_ext)).
+ simpl.
  refine (fun p γ γε => _).
  refine (@ext_rel_ext _ _ _ _ _ _ (γε p !) p !).
Defined.

Definition Prd {Γ : Ctx} (A : Typ Γ) (B : Typ (Ext Γ A)) : Typ Γ.
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => _).
  refine (forall
    (x : forall q (α : q ≤ p), A q (α · γ) (α · γε))
    (xε : forall q (α : q ≤ p), @typ_rel Γ A _ (α · γ) (α · γε) (α · x)), _).
  unshelve refine (B.(typ_typ _) p _ _).
  - refine (Build_Ext_typ₀ γ γε x xε).
  - simpl; unshelve econstructor; simpl.
    { reflexivity. }
    { refine (α · xε). }
+ simpl.
  refine (fun p γ γε f => _).
  unshelve refine (
    forall
      q (α : q ≤ p)
      (x : forall r (β : r ≤ q), A r ((β ∘ α) · γ) ((β ∘ α) · γε))
      (xε : forall r (β : r ≤ q), @typ_rel _ A r ((β ∘ α) · γ) ((β ∘ α) · γε) (β · x)),
      @typ_rel _ B q _ _ _
  ).
  - refine (Build_Ext_typ₀ (α · γ) (α · γε) x xε).
  - simpl; intros r β; unshelve econstructor; simpl.
    { reflexivity. }
    { refine (β · xε). }
  - simpl.
    refine (fun r β => f r (β ∘ α) (β · x) (β · xε)).
Defined.

Definition Lam {Γ : Ctx} (A : Typ Γ) {B : Typ (Ext Γ A)}
  (t : Trm (Ext Γ A) B) : Trm Γ (Prd A B).
Proof.
unshelve econstructor.
+ refine (fun p γ γε x xε => _); simpl.
  unshelve refine (t.(trm_elt) p _ _).
+ simpl.
  refine (fun p γ γε q α x xε => _).
  unshelve refine (t.(trm_rel) _ _ _).
Defined.

Definition App {Γ : Ctx} {A : Typ Γ} {B : Typ (Ext Γ A)}
  (t : Trm Γ (Prd A B)) (u : Trm Γ A) : Trm Γ (Typ_subs (Cns _ _ u) B).
Proof.
unshelve econstructor.
+ refine (fun p γ γε => _); simpl.
  unshelve refine (t.(trm_elt) p γ γε _ (fun q α => u.(trm_rel) q (α · γ) (α · γε))).
+ simpl. refine (fun p γ γε => _).
  unshelve refine (t.(trm_rel) p _ _ _ _ _  (fun q α => u.(trm_rel) q (α · γ) (α · γε))).
Defined.

Lemma Lam_App_eqn :
  forall (Γ : Ctx) (A : Typ Γ) (B : Typ (Ext Γ A)) (t : Trm (Ext Γ A) B) (u : Trm Γ A),
  App (Lam A t) u = Trm_subs (Cns _ _ u) t.
Proof.
reflexivity.
Qed.

Lemma App_Lam_eqn :
  forall (Γ : Ctx) (A : Typ Γ) (B : Typ (Ext Γ A))
  (t : Trm Γ (Prd A B)),
  Lam A (@App (Ext Γ A) (Typ_subs (Wkn Γ A) A) (Typ_subs (Lft (Wkn Γ A) A) B) (Trm_subs (Wkn Γ A) t) Var) = t.
Proof.
reflexivity.
Qed.

(** Universes *)

Record TYPE@{i} (p : ℙ) : Type@{i+1} := {
  elt : forall q (α : q ≤ p), Type@{i};
  rel : (forall q (α : q ≤ p), elt q α) -> SProp;
}.

Arguments elt {_}.
Arguments rel {_}.

Definition Unv {Γ : Ctx} : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun p γ γε => TYPE p).
+ simpl; refine (fun p γ γε A => _).
  refine (eqn (fun q (α : q ≤ p) => ((A q α).(elt) q !)) ((A p !).(elt))).
Defined.

Definition Elt {Γ : Ctx} (A : Trm Γ Unv) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun p γ γε => (A.(trm_elt) p γ γε).(elt) p !).
+ simpl; unshelve refine (fun p γ γε x => _).
  refine ((A.(trm_elt) p γ γε).(rel) _).
  refine (eqn_rect (fun A₀ _ => forall q (α : q ≤ p), A₀ q α) x (A.(trm_rel) p γ γε)).
Defined.

Definition Rfl {Γ : Ctx} (A : Typ Γ) : Trm Γ Unv.
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => _).
  unshelve econstructor.
  - refine (fun q α => A.(typ_typ _) q (α · γ) (α · γε)).
  - refine (A.(typ_rel)).
+ reflexivity.
Defined.

Lemma Rfl_Elt : forall (Γ : Ctx) (A : Typ Γ), Elt (Rfl A) = A.
Proof.
reflexivity.
Qed.

(** Helper *)

Definition Build_trm_aux {Γ : Ctx} (A : Typ Γ)
  (x : forall (p : ℙ)
    (γ : forall q (α : q ≤ p), Γ q)
    (γε : forall q (α : q ≤ p), (ctx_rel Γ) (α · γ)),
    exist
    (forall q (α : q ≤ p), A q (α · γ) (α · γε))
    (fun x => forall q (α : q ≤ p), @typ_rel _ A q (α · γ) (α · γε) (α · x)))
  (xε : forall p
    (γ : forall q (α : q ≤ p), Γ q)
    (γε : forall q (α : q ≤ p), (ctx_rel Γ) (α · γ)),
(*     typ_rel A (val (x p γ γε)) -> *)
(*     typ_rel A (fun (q : ℙ) (α : q ≤ p) => val (x q (α · γ) (α · γε)) q !)) *)
    eqn ((x p γ γε).(val)) (fun q (α : q ≤ p) => (x q (α · γ) (α · γε)).(val) q !))
  : Trm Γ A.
Proof.
unshelve econstructor.
+ intros p γ γε.
  refine ((x p γ γε).(val) p !).
+ simpl; intros p γ γε.
(*   refine (xε p γ γε ((x p γ γε).(spc) p !)). *)
  refine (rew (fun x₀ => typ_rel A x₀) (xε p γ γε) _).
  refine ((x p γ γε).(spc) p !).
Defined.

Definition Ext_elim₀  {Γ : Ctx} (A : Typ Γ) (p : ℙ)
  (P : forall
    (γ : forall q : ℙ, q ≤ p -> Ext Γ A q)
    (γε : forall (q : ℙ) (α : q ≤ p), ctx_rel (Ext Γ A) (α · γ)), Type)
  (u : forall
    (γ : forall q (α : q ≤ p) r (β : r ≤ q), Γ r)
    (γε : forall q (α : q ≤ p) r (β : r ≤ q), ctx_rel Γ (β · (γ q α)))
    (x : forall q (α : q ≤ p), A q (γ q α) (γε q α))
    (γe : Fε γ)
    (xε : forall q (α : q ≤ p), @typ_rel Γ A q (evl (α · γ) q !) (α · Θ γ γε γe) (letΘ (α · γ) (α · γε) (α • γe) (α · x))),
    P
    (fun q α => Build_Ext_typ Γ A q (γ q α) (γε q α) (x q α))
    (fun q α => Build_Ext_rel Γ A q (α · γ) (α · γε) (α · x) (α • γe) (α · xε))

  )
  (γ : forall q (α : q ≤ p), Ext Γ A q)
  (γε : forall q (α : q ≤ p), ctx_rel (Ext Γ A) (α · γ)) :
  P γ γε.
Proof.
refine (u
  (fun q α r β => (γ q α).(ext_typ_ctx) r β)
  (fun q α r β => (γ q α).(ext_typ_rel) r β)
  (fun q α => (γ q α).(ext_typ_ext))
  ((γε p !).(ext_rel_ctx))
  (fun q α => (γε q α).(ext_rel_ext) q !)
).
Defined.

Definition Ext_elim₀_s  {Γ : Ctx} (A : Typ Γ) (p : ℙ)
  (P : forall
    (γ : forall q : ℙ, q ≤ p -> Ext Γ A q)
    (γε : forall (q : ℙ) (α : q ≤ p), ctx_rel (Ext Γ A) (α · γ)), SProp)
  (u : forall
    (γ : forall q (α : q ≤ p) r (β : r ≤ q), Γ r)
    (γε : forall q (α : q ≤ p) r (β : r ≤ q), ctx_rel Γ (β · (γ q α)))
    (x : forall q (α : q ≤ p), A q (γ q α) (γε q α))
    (γe : Fε γ)
    (xε : forall q (α : q ≤ p), @typ_rel Γ A q (evl (α · γ) q !) (α · Θ γ γε γe) (letΘ (α · γ) (α · γε) (α • γe) (α · x))),
    P
    (fun q α => Build_Ext_typ Γ A q (γ q α) (γε q α) (x q α))
    (fun q α => Build_Ext_rel Γ A q (α · γ) (α · γε) (α · x) (α • γe) (α · xε))

  )
  (γ : forall q (α : q ≤ p), Ext Γ A q)
  (γε : forall q (α : q ≤ p), ctx_rel (Ext Γ A) (α · γ)) :
  P γ γε.
Proof.
refine (u
  (fun q α r β => (γ q α).(ext_typ_ctx) r β)
  (fun q α r β => (γ q α).(ext_typ_rel) r β)
  (fun q α => (γ q α).(ext_typ_ext))
  ((γε p !).(ext_rel_ctx))
  (fun q α => (γε q α).(ext_rel_ext) q !)
).
Defined.

Definition Build_Ext_rel₀ {Γ : Ctx} {A : Typ Γ} {p : ℙ}
  (γ : forall q (α : q ≤ p), Γ q)
  (γε : forall q (α : q ≤ p), ctx_rel Γ (α · γ))
  (x : forall q (α : q ≤ p), A q (α · γ) (α · γε))
  (xε : forall q (α : q ≤ p), @typ_rel _ A q (α · γ) (α · γε) (α · x))
  : forall (q : ℙ) (α : q ≤ p),
     ctx_rel (Ext Γ A) (α · Build_Ext_typ₀ γ γε x xε).
Proof.
refine (fun q α =>
  Build_Ext_rel Γ A q (α · ret γ)
    (fun r β s ζ => γε s (ζ ∘ β ∘ α)) (α · x) (refl _ _) (α · xε)
).
Defined.

Definition Build_lam_aux {Γ : Ctx} (A : Typ Γ) (B : Typ (Ext Γ A))
  (f : forall (p : ℙ)
    (γ : forall q : ℙ, q ≤ p -> Γ q)
    (γε : forall (q : ℙ) (α : q ≤ p), ctx_rel Γ (α · γ))
    (x : forall (q : ℙ) (α : q ≤ p), A q (α · γ) (α · γε))
    (xε : forall (q : ℙ) (α : q ≤ p), @typ_rel _ A _ (α · γ) (α · γε) (α · x)),
    exist
    (forall q (α : q ≤ p), B q (Build_Ext_typ₀ (α · γ) (α · γε) (α · x) (α · xε))
      (Build_Ext_rel₀ (α · γ) (α · γε) (α · x) (α · xε)))
    (fun y => forall (q : ℙ) (α : q ≤ p),
      @typ_rel (Ext Γ A) B _
        (Build_Ext_typ₀ (α · γ) (α · γε) (α · x) (α · xε))
        (Build_Ext_rel₀ (α · γ) (α · γε) (α · x) (α · xε))
        (α · y)
    )
  )
  (fε :
    forall (p : ℙ)
      (γ : forall q : ℙ, q ≤ p -> Γ q)
      (γε : forall (q : ℙ) (α : q ≤ p), ctx_rel Γ (α · γ))
      (x : forall (q : ℙ) (α : q ≤ p), A q (α · γ) (α · γε))
      (xε : forall (q : ℙ) (α : q ≤ p), @typ_rel _ A q (α · γ) (α · γε) (α · x)),
    eqn
      (@val _ _ (f p γ γε x xε))
      (fun (q : ℙ) (α : q ≤ p) => @val _ _ (f q (α · γ) (α · γε) (α · x) (α · xε)) q !)
  )
  : Trm Γ (Prd A B).
Proof.
unshelve refine (Lam _ _).
unshelve refine (Build_trm_aux _ (fun p => _) _).
+ refine (@Ext_elim₀ Γ A p _ _).
  intros γ γε x γe; revert γ γe γε x.
  refine (F_rect _ _).
  intros γ γε x xε.
  unshelve econstructor.
  refine ((f p γ (γε p !) x xε).(val)).
  refine ((f p γ (γε p !) x xε).(spc)).
+ intros; simpl.
  unfold Ext_elim₀; simpl.
  revert γ γε.
  unshelve refine (Ext_elim₀_s _ _ _ _).
  intros γ γε x γe; revert γ γe γε x.
  refine (F_sind _ _); intros γ γε x xε; simpl in *.
  refine (fε p γ (γε _ _) x xε).
Defined.

Lemma Build_lam_aux_App : forall Γ A B f fε (u : Trm Γ A),
  @trm_elt _ _ (@App Γ A B (@Build_lam_aux Γ A B f fε) u) =
  (fun p γ γε => (f p γ γε (fun q α => u.(trm_elt) q (α · γ) (α · γε)) (fun q α => u.(trm_rel) q (α · γ) (α · γε))).(val) p !).
Proof.
reflexivity.
Qed.

(** Sum type *)

Inductive Sum₀ {p : ℙ} (A B : forall q (α : q ≤ p), Type) :=
| Inl₀ : forall (x : forall q (α : q ≤ p), A q α), Sum₀ A B
| Inr₀ : forall (y : forall q (α : q ≤ p), B q α), Sum₀ A B.

Inductive Sumε {p : ℙ}
  (A : forall q (α : q ≤ p), Type)
  (Aε : forall q (α : q ≤ p), (forall r (β : r ≤ q), A r (β ∘ α)) -> SProp)
  (B : forall q (α : q ≤ p), Type)
  (Bε : forall q (α : q ≤ p), (forall r (β : r ≤ q), B r (β ∘ α)) -> SProp)
  : (forall q (α : q ≤ p), Sum₀ (α · A) (α · B)) -> SProp :=
| Inlε : forall
  (x : forall q (α : q ≤ p), A q α)
  (xε : forall q (α : q ≤ p), Aε q α (α · x)), Sumε A Aε B Bε (fun q α => Inl₀ _ _ (α · x))
| Inrε : forall
  (y : forall q (α : q ≤ p), B q α)
  (yε : forall q (α : q ≤ p), Bε q α (α · y)), Sumε A Aε B Bε (fun q α => Inr₀ _ _ (α · y))
.

Definition Sum {Γ : Ctx} (A B : Typ Γ) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun p γ γε => @Sum₀ p (fun q α => A q (α · γ) (α · γε)) (fun q α => B q (α · γ) (α · γε))).
+ refine (fun p γ γε s => _).
  refine (@Sumε p
    (fun q α => A q (α · γ) (α · γε)) (fun q α => @typ_rel Γ A q (α · γ) (α · γε))
    (fun q α => B q (α · γ) (α · γε)) (fun q α => @typ_rel Γ B q (α · γ) (α · γε))
    s
  ).
Defined.

Definition Inl {Γ : Ctx} {A B : Typ Γ} : Trm Γ (Prd A (Typ_subs (Wkn Γ A) (Sum A B))).
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε x xε => Inl₀ _ _ x).
+ refine (fun p γ γε q α x xε => Inlε _ _ _ _ x xε).
Defined.

Definition Inr {Γ : Ctx} {A B : Typ Γ} : Trm Γ (Prd B (Typ_subs (Wkn Γ B) (Sum A B))).
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε y yε => Inr₀ _ _ y).
+ refine (fun p γ γε q α y yε => Inrε _ _ _ _ y yε).
Defined.

(* Definition Sum_Inl_inv (p : ℙ)
    (s : forall q : ℙ, q ≤ p -> Inl₀ q)
    (sε : forall (q : ℙ) (α : q ≤ p), Natε (α · n))
    (e : eqn (Inl₀ p) (n p !)) :
    eqn (fun q _ => O₀ q) n.
Proof.
 *)

Definition Sum_rect {Γ : Ctx} (A B : Typ Γ)
  (P : Trm Γ (Prd (Sum A B) Unv))
  (pL : Trm Γ
    (Prd A
      (Elt (@App (Ext Γ A) (Typ_subs (Wkn _ _) (Sum A B)) Unv (Trm_subs (Wkn _ _) P)
      (@App (Ext Γ A) (Typ_subs (Wkn Γ A) A) (Typ_subs (Cmp (Wkn _ _) (Wkn _ _)) (Sum A B)) (@Inl _ _ (Typ_subs (Wkn Γ A) B)) (@Var Γ A))))
    )
  )
  (pR : Trm Γ
    (Prd B
      (Elt (@App (Ext Γ B) (Typ_subs (Wkn _ _) (Sum A B)) Unv (Trm_subs (Wkn _ _) P)
      (@App (Ext Γ B) (Typ_subs (Wkn Γ B) B) (Typ_subs (Cmp (Wkn _ _) (Wkn _ _)) (Sum A B)) (@Inr _ (Typ_subs (Wkn Γ B) A) _) (@Var Γ B))))
    )
  )
  :
  Trm Γ (Prd (Sum A B) (Elt ((@App _ (Typ_subs (Wkn _ _) (Sum A B)) Unv (Trm_subs (Wkn _ _) P)) (@Var _ (Sum A B))))).
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε s sε => _).
  generalize (refl _ (s p !)).
  generalize (s p !) at 1 as s₀.
  destruct s₀ as [x₀|y₀]; intros e₀.
  - assert (e₁ : eqn (fun q (α : q ≤ p) => Inl₀ _ _ (α · x₀)) s).
    { refine (
        match sε p ! in Sumε _ _ _ _ s₁ return
          eqn _ (s₁ p !) -> eqn _ s₁
        with
        | Inlε _ _ _ _ x xε => _
        | Inrε _ _ _ _ y yε => _
      end e₀); clear e₀; intros e₀.
      + assert (e₁: eqn x₀ x).
        { refine (match e₀ in eqn _ s₁ return match s₁ return SProp with Inl₀ _ _ x => eqn x₀ x | Inr₀ _ _ _ => True end with refl _ _ => refl _ _ end). }
        destruct e₁; reflexivity.
      + elimtype False.
        refine (match e₀ in eqn _ s₁ return match s₁ return SProp with Inl₀ _ _ x => True | Inr₀ _ _ _ => False end with refl _ _ => I end).
    }
    destruct e₁.
    refine (pL.(trm_elt) p γ γε x₀ _).
    { refine (
        match sε p ! in Sumε _ _ _ _ s₁ return
          match s₁ p ! return SProp with Inl₀ _ _ x₀ => forall q α, typ_rel A (α · x₀) | Inr₀ _ _ _ => True end
        with 
        | Inlε _ _ _ _ x xε => xε
        | Inrε _ _ _ _ y yε => I
      end). }
  - assert (e₁ : eqn (fun q (α : q ≤ p) => Inr₀ _ _ (α · y₀)) s).
    { refine (
        match sε p ! in Sumε _ _ _ _ s₁ return
          eqn _ (s₁ p !) -> eqn _ s₁
        with
        | Inlε _ _ _ _ x xε => _
        | Inrε _ _ _ _ y yε => _
      end e₀); clear e₀; intros e₀.
      + elimtype False.
        refine (match e₀ in eqn _ s₁ return match s₁ return SProp with Inl₀ _ _ x => False | Inr₀ _ _ _ => True end with refl _ _ => I end).
      + assert (e₁: eqn y₀ y).
        { refine (match e₀ in eqn _ s₁ return match s₁ return SProp with Inl₀ _ _ x => True | Inr₀ _ _ y => eqn y₀ y end with refl _ _ => refl _ _ end). }
        destruct e₁; reflexivity.
    }
    destruct e₁.
    refine (pR.(trm_elt) p γ γε y₀ _).
    { refine (
        match sε p ! in Sumε _ _ _ _ s₁ return
          match s₁ p ! return SProp with Inr₀ _ _ y₀ => forall q α, typ_rel B (α · y₀) | Inl₀ _ _ _ => True end
        with 
        | Inlε _ _ _ _ x xε => I
        | Inrε _ _ _ _ y yε => yε
      end). }
+ intros p γ γε q α s sε. simpl.
  assert (sε₀ := sε q !).
  match type of sε₀ with Sumε _ _ _ _ ?s₀ => change s₀ with s in sε₀ end. 
  destruct sε₀ as [x xε|y yε]; simpl.
  - refine (pL.(trm_rel) q (α · γ) (α · γε) q ! x xε).
  - refine (pR.(trm_rel) q (α · γ) (α · γε) q ! y yε).
Defined.

Lemma Sum_rect_Inl : forall
  (Γ : Ctx) (A B : Typ Γ)
  (P : Trm Γ (Prd (Sum A B) Unv))
  (P : Trm Γ (Prd (Sum A B) Unv))
  (pL : Trm Γ
    (Prd A
      (Elt (@App (Ext Γ A) (Typ_subs (Wkn _ _) (Sum A B)) Unv (Trm_subs (Wkn _ _) P)
      (@App (Ext Γ A) (Typ_subs (Wkn Γ A) A) (Typ_subs (Cmp (Wkn _ _) (Wkn _ _)) (Sum A B)) (@Inl _ _ (Typ_subs (Wkn Γ A) B)) (@Var Γ A))))
    )
  )
  (pR : Trm Γ
    (Prd B
      (Elt (@App (Ext Γ B) (Typ_subs (Wkn _ _) (Sum A B)) Unv (Trm_subs (Wkn _ _) P)
      (@App (Ext Γ B) (Typ_subs (Wkn Γ B) B) (Typ_subs (Cmp (Wkn _ _) (Wkn _ _)) (Sum A B)) (@Inr _ (Typ_subs (Wkn Γ B) A) _) (@Var Γ B))))
    )
  )
  (x : Trm Γ A),
  (App (Sum_rect A B P pL pR) (App Inl x)) = App pL x.
Proof.
reflexivity.
Qed.

Lemma Sum_rect_Inr : forall
  (Γ : Ctx) (A B : Typ Γ)
  (P : Trm Γ (Prd (Sum A B) Unv))
  (P : Trm Γ (Prd (Sum A B) Unv))
  (pL : Trm Γ
    (Prd A
      (Elt (@App (Ext Γ A) (Typ_subs (Wkn _ _) (Sum A B)) Unv (Trm_subs (Wkn _ _) P)
      (@App (Ext Γ A) (Typ_subs (Wkn Γ A) A) (Typ_subs (Cmp (Wkn _ _) (Wkn _ _)) (Sum A B)) (@Inl _ _ (Typ_subs (Wkn Γ A) B)) (@Var Γ A))))
    )
  )
  (pR : Trm Γ
    (Prd B
      (Elt (@App (Ext Γ B) (Typ_subs (Wkn _ _) (Sum A B)) Unv (Trm_subs (Wkn _ _) P)
      (@App (Ext Γ B) (Typ_subs (Wkn Γ B) B) (Typ_subs (Cmp (Wkn _ _) (Wkn _ _)) (Sum A B)) (@Inr _ (Typ_subs (Wkn Γ B) A) _) (@Var Γ B))))
    )
  )
  (y : Trm Γ B),
  (App (Sum_rect A B P pL pR) (App Inr y)) = App pR y.
Proof.
reflexivity.
Qed.

(** Natural numbers *)

Inductive Nat₀ (p : ℙ) :=
| O₀ : Nat₀ p
| S₀ : forall (n : forall q (α : q ≤ p), Nat₀ q), Nat₀ p.

Inductive Natε {p : ℙ} : (forall q (α : q ≤ p), Nat₀ q) -> SProp :=
| Oε : Natε (fun q _ => O₀ q)
| Sε : forall (n : forall q (α : q ≤ p), Nat₀ q) (nε : forall q (α : q ≤ p), Natε (α · n)),
      Natε (fun q α => S₀ q (α · n)).

Definition Nat {Γ : Ctx} : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun p γ γε => _).
  exact (Nat₀ p).
+ refine (fun p γ γε n => _).
  exact (Natε n).
Defined.

Definition O {Γ : Ctx} : Trm Γ Nat.
Proof.
unshelve econstructor.
+ refine (fun p γ γε => O₀ p).
+ simpl; refine (fun p γ γε => Oε).
Defined.

Definition S {Γ : Ctx} : Trm Γ (Prd Nat Nat).
Proof.
unshelve econstructor.
+ simpl; refine (fun p γ γε n nε => S₀ p n).
+ simpl; refine (fun p γ γε q α n nε => Sε n nε).
Defined.

Definition Nat_O_inv (p : ℙ)
    (n : forall q : ℙ, q ≤ p -> Nat₀ q)
    (nε : forall (q : ℙ) (α : q ≤ p), Natε (α · n))
    (e : eqn (O₀ p) (n p !)) :
    eqn (fun q _ => O₀ q) n.
Proof.
specialize (nε p !).
change (Natε n) in nε.
destruct nε.
+ reflexivity.
+ let t := match type of e with eqn _ ?t => t end in
  elimtype False;
  change (match t with O₀ _ => True | S₀ _ n => False end).
  destruct e; constructor.
Qed.

Definition Nat_S_inv (p : ℙ)
    (n : forall q : ℙ, q ≤ p -> Nat₀ q)
    (nε : forall (q : ℙ) (α : q ≤ p), Natε (α · n))
    (m : forall q : ℙ, q ≤ p -> Nat₀ q)
    (e : eqn (S₀ p m) (n p !)) :
    eqn (fun q α => S₀ q (α · m)) n.
Proof.
specialize (nε p !).
change (Natε n) in nε.
destruct nε.
+ let t := match type of e with eqn _ ?t => t end in
  elimtype False;
  change (match t with S₀ _ _ => True | O₀ _ => False end).
  destruct e; constructor.
+ refine (
    match e in eqn _ z return
      match z return SProp with
      | O₀ _ => True
      | S₀ _ n₀ => eqn (fun q α => S₀ q (α · m)) (fun q α => S₀ q (α · n₀))
      end
    with refl _ _ => refl _ _ end
  ).
Qed.

Definition Natε_S_inv (p : ℙ)
  (n : forall q : ℙ, q ≤ p -> Nat₀ q)
  (nε : forall (q : ℙ) (α : q ≤ p), Natε (fun r β => S₀ r ((β ∘ α) · n))) :
  forall q (α : q ≤ p), Natε (α · n).
Proof.
specialize (nε p !).
refine (
match nε in Natε n₀ return
  match n₀ p ! return SProp with
  | O₀ _ => True
  | S₀ _ m₀ => forall q α, Natε (α · m₀)
  end
with
| Oε => I
| Sε _ mε => mε
end
).
Defined.

Definition Nat_rect {Γ : Ctx}
  (P : Trm Γ (Prd Nat Unv))
  (pO : Trm Γ (Elt (App P O)))
  (pS : Trm Γ
    (Prd Nat
    (Prd (Elt (@App _ Nat Unv (Trm_subs (Wkn _ _) P) (@Var _ Nat)))
      (Elt (@App _ Nat Unv ((Trm_subs (Wkn (Ext Γ Nat) _)
      (Trm_subs (Wkn Γ Nat) P))) (App S (Trm_subs (Wkn (Ext Γ Nat) _) Var)))))))
  :
  Trm Γ (Prd Nat (Elt ((@App _ Nat Unv (Trm_subs (Wkn _ _) P)) (@Var _ Nat)))).
Proof.
unshelve refine (Build_lam_aux _ _ _ _); simpl in *.
+ intros p γ γε n nε. simpl in n, nε.
  generalize (refl _ (n p !)).
  generalize (n p !) at 1 as n₀.
  induction n₀ as [|p n₀ IHn₀]; intros e₀.
  - simpl. unshelve econstructor.

    * refine (fun q α => _).

      pose (e₁ := Nat_O_inv _ n nε e₀).

      destruct e₁.

      refine (pO.(trm_elt) q (α · γ) (α · γε)).

    * pose (e₁ := Nat_O_inv _ n nε e₀).
      destruct e₁; simpl.
      refine (fun q α => pO.(trm_rel) q (α · γ) (α · γε)).

  - unshelve econstructor.

    * refine (fun q α => _).
      pose (e₁ := Nat_S_inv _ n nε n₀ e₀).
      destruct e₁.
      unshelve refine (pS.(trm_elt) q (α · γ) (α · γε) (α · n₀) (Natε_S_inv _ (α · n₀) (α · nε)) _ _).
      { unshelve refine (α · (IHn₀ p ! γ γε _ (Natε_S_inv _ n₀ nε) (refl _ _)).(val)). }
      { unshelve refine (α · (IHn₀ p ! γ γε _ (Natε_S_inv _ n₀ nε) (refl _ _)).(spc)). }

    * revert γ γe γε nε.
      refine (F_sind _ _); intros γ γε nε q α.
      pose (e₁ := Nat_S_inv _ n nε n₀ e₀).
      destruct e₁.

      unshelve refine (
        pS.(trm_rel) q (α · γ) (γε q α) q !
          (α · n₀) (Natε_S_inv _ (α · n₀) (α · nε)) q !
          (α · (IHn₀ p ! (ret γ) γε _ (refl _ _) (Natε_S_inv _ n₀ nε) (refl _ _)).(val))
          (α · (IHn₀ p ! (ret γ) γε _ (refl _ _) (Natε_S_inv _ n₀ nε) (refl _ _)).(spc))
      ).



unshelve refine (Lam _ _).
unshelve refine (Build_trm_aux _ (fun p => _) _).
+ refine (@Ext_elim₀ Γ Nat p _ _).
  intros γ γε n γe nε. simpl in n, nε.
  generalize (refl _ (n p !)).
  generalize (n p !) at 1 as n₀.
  induction n₀ as [|p n₀ IHn₀]; intros e₀.
  - simpl. unshelve econstructor.

    * refine (fun q α => _).
      change (
        elt
          (trm_elt P q (evl γ q α)
             (α · (Θ γ γε γe))
             (α · (@letΘ Γ Nat _ γ γε γe n)) (α · nε)) q !
      ).
      change (forall q (α : q ≤ p), Natε (α · (@letΘ _ Nat _ γ γε γe n))) in nε.

      revert γ γe γε nε; refine (F_rect _ _); simpl; intros γ γε nε.

      pose (e₁ := Nat_O_inv _ n nε e₀).

      destruct e₁.

      refine (pO.(trm_elt) q (α · γ) (γε q α)).

    * revert γ γe γε nε.
      refine (F_sind _ _); simpl; intros γ γε nε q α.
      pose (e₁ := Nat_O_inv _ n nε e₀).
      destruct e₁; simpl.
      refine (pO.(trm_rel) _ _ _).

  - unshelve econstructor.

    * refine (fun q α => _).
      revert γ γe γε nε; refine (F_rect _ _); simpl; intros γ γε nε.
      pose (e₁ := Nat_S_inv _ n nε n₀ e₀).
      destruct e₁.
      unshelve refine (pS.(trm_elt) q (α · γ) (γε q α) (α · n₀) (Natε_S_inv _ (α · n₀) (α · nε)) _ _).
      { unshelve refine (α · (IHn₀ p ! (ret γ) γε _ (refl _ _) (Natε_S_inv _ n₀ nε) (refl _ _)).(val)). }
      { unshelve refine (α · (IHn₀ p ! (ret γ) γε _ (refl _ _) (Natε_S_inv _ n₀ nε) (refl _ _)).(spc)). }      

    * revert γ γe γε nε.
      refine (F_sind _ _); intros γ γε nε q α.
      pose (e₁ := Nat_S_inv _ n nε n₀ e₀).
      destruct e₁.

      unshelve refine (
        pS.(trm_rel) q (α · γ) (γε q α) q !
          (α · n₀) (Natε_S_inv _ (α · n₀) (α · nε)) q !
          (α · (IHn₀ p ! (ret γ) γε _ (refl _ _) (Natε_S_inv _ n₀ nε) (refl _ _)).(val))
          (α · (IHn₀ p ! (ret γ) γε _ (refl _ _) (Natε_S_inv _ n₀ nε) (refl _ _)).(spc))
      ).

+ intros p.
  refine (Ext_elim₀_s _ _ _ _).
  intros γ γε n γe; revert γ γe γε n.
  refine (F_sind _ _).
  intros γ γε n nε.
  simpl in n, nε.
  assert (nε₀ := nε p !).
  change (Natε n) in nε₀.
  induction nε₀.
  - reflexivity.
  - admit. (* FIXME *)
Defined.

Lemma Nat_rect_O : forall
  (Γ : Ctx)
  (P : Trm Γ (Prd Nat Unv))
  (pO : Trm Γ (Elt (App P O)))
  (pS : Trm Γ
    (Prd Nat
    (Prd (Elt (@App _ Nat Unv (Trm_subs (Wkn _ _) P) (@Var _ Nat)))
      (Elt (@App _ Nat Unv ((Trm_subs (Wkn (Ext Γ Nat) _)
      (Trm_subs (Wkn Γ Nat) P))) (App S (Trm_subs (Wkn (Ext Γ Nat) _) Var))))))),
  (App (Nat_rect P pO pS) O) = pO.
Proof.
reflexivity.
Qed.

Lemma Nat_rect_S : forall
  (Γ : Ctx)
  (P : Trm Γ (Prd Nat Unv))
  (pO : Trm Γ (Elt (App P O)))
  (pS : Trm Γ
    (Prd Nat
    (Prd (Elt (@App _ Nat Unv (Trm_subs (Wkn _ _) P) (@Var _ Nat)))
      (Elt (@App _ Nat Unv ((Trm_subs (Wkn (Ext Γ Nat) _)
      (Trm_subs (Wkn Γ Nat) P))) (App S (Trm_subs (Wkn (Ext Γ Nat) _) Var)))))))
  (n : Trm Γ Nat),
  App (Nat_rect P pO pS) (App S n) =
  @App _ (Elt (App P n)) (Typ_subs (Wkn _ _) (Elt (App P (App S n)))) (App pS n) (App (Nat_rect P pO pS) n).
Proof.
Fail reflexivity (* fails *)
Abort.
