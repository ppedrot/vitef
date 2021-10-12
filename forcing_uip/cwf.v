Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Axiom F : False.
Ltac admit := case F.

Inductive True : SProp := I.
Inductive and (A : SProp) (B : SProp) : SProp := conj : A -> B -> and A B.

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

Record Ext_rel (Γ : Ctx) (A : Typ Γ) (p : ℙ)
  (γ : forall q : ℙ, q ≤ p -> Ext_typ Γ A q) : SProp := {

  ext_rel_ctx :
    forall q (α : q ≤ p),
      eqn (γ q α).(ext_typ_ctx) (fun r (β : r ≤ q) => (γ r (β ∘ α)).(ext_typ_ctx) r !);

  ext_rel_ext :

    forall q (α : q ≤ p),
    @typ_rel _ A q
      (fun r (β : r ≤ q) => (γ r (β ∘ α)).(ext_typ_ctx) r !)
      (rew
        (fun γ₀ => forall r (β : r ≤ q), ctx_rel Γ (β · γ₀))
        (ext_rel_ctx q α)
        ((γ q α).(ext_typ_rel))
      )
      (fun r (β : r ≤ q) =>
        eqn_rect
          (fun
            (γ₀ : forall q : ℙ, q ≤ r -> Γ q)
            (e₀ : eqn (ext_typ_ctx (γ r (β ∘ α))) γ₀) =>
              A r γ₀ (rew (fun γ₀ => forall (s : ℙ) (ζ : s ≤ r), ctx_rel Γ (ζ · γ₀)) e₀ _)
        )
        (γ r (β ∘ α)).(ext_typ_ext)
        (ext_rel_ctx r (β ∘ α))
      )

}.

Arguments ext_rel_ctx {_ _ _ _}.
Arguments ext_rel_ext {_ _ _ _}.

Definition Θ {Γ : Ctx} (p : ℙ)
  (γ : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), Γ r)
  (γε : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), ctx_rel Γ (β · (γ q α)))
  (γe : forall q (α : q ≤ p), eqn (γ q α) (fun r (β : r ≤ q) => (γ r (β ∘ α)) r !)) :
  forall (q : ℙ) (α : q ≤ p),
    ctx_rel Γ (fun  (r : ℙ) (β : r ≤ q) => γ r (β ∘ α) r !) :=
  rew (fun γ₀ => forall q (α : q ≤ p), ctx_rel Γ (α · γ₀)) (γe p !) (γε p !).
(*
Definition FreeE {Γ : Ctx} (p : ℙ)
  (γ : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), Γ r)
  (γε : forall (q : ℙ) (α : q ≤ p) r (β : r ≤ q), ctx_rel Γ (β · (γ q α)))
  (γe : forall q (α : q ≤ p), eqn (γ q α) (fun r (β : r ≤ q) => (γ r (β ∘ α)) r !))
  (A : forall
    (γ : forall q : ℙ, q ≤ p -> Γ q)
    (γε : forall (q : ℙ) (α : q ≤ p), ctx_rel Γ (α · γ)), Type)
  (x : forall q (α : q ≤ p), A (γ p !) (γε p !))
  :
  True.
Proof.

pose (fun q (α : q ≤ p) r (β : r ≤ q) =>
        eqn_rect
          (fun
            (γ₀ : forall q : ℙ, q ≤ r -> Γ q)
            (e₀ : eqn ((γ r (β ∘ α))) γ₀) =>
              A r γ₀ (rew (fun γ₀ => forall (s : ℙ) (ζ : s ≤ r), ctx_rel Γ (ζ · γ₀)) e₀ _)
        )
        (γ r (β ∘ α)).(ext_typ_ext)
        (ext_rel_ctx r (β ∘ α))
      ).
*)

Definition Ext (Γ : Ctx) (A : Typ Γ) : Ctx.
Proof.
unshelve econstructor.
+ refine (Ext_typ Γ A).
+ refine (Ext_rel Γ A).
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
  refine (rew (fun γ₀ => ctx_rel Γ γ₀) ((γε p !).(ext_rel_ctx) p !) _).
  refine ((γ p !).(ext_typ_rel) p !).
Defined.

Definition Lft {Γ Δ : Ctx} (σ : Sub Γ Δ) (A : Typ Δ) :
  Sub (Ext Γ (Typ_subs σ A)) (Ext Δ A).
Proof.
unshelve econstructor.
+ unshelve refine (fun p γ γε => Build_Ext_typ _ _ _ _ _ _); simpl in *.
  - unshelve refine (fun q α => σ q (fun r (β : r ≤ q) => (γ r (β ∘ α)).(ext_typ_ctx) r !) _).

(*     refine (Θ _ _ (fun r β => (γ r (β ∘ α)).(ext_typ_rel)) (fun r β => (γε r (β ∘ α)).(ext_rel_ctx) r !)). *)
    refine ((rew
            (fun γ₀ => forall r (β : r ≤ q), ctx_rel Γ (β · γ₀))
            (ext_rel_ctx (γε q α) q !)
            ((γ q α).(ext_typ_rel))
          )
    ).
  - refine (fun q α => σ.(sub_rel) q
      (fun r (β : r ≤ q) => (γ r (β ∘ α)).(ext_typ_ctx) r !)
      (rew (fun γ₀ => forall r (β : r ≤ q), ctx_rel Γ (β · γ₀)) ((γε q α).(ext_rel_ctx) q !) (γ q α).(ext_typ_rel))
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
      ) ((γ p !).(ext_typ_ext)) (ext_rel_ctx (γε p !) p !)
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
  refine (
    eqn_rect
      (fun γ₀ (e₀ : eqn (ext_typ_ctx (γ p !)) γ₀) =>
        A p γ₀ (rew (fun γ₀ => forall q (α : q ≤ p), ctx_rel Γ (α · γ₀)) e₀ (γ p !).(ext_typ_rel))
      )
      (γ p !).(ext_typ_ext)
      ((γε p !).(ext_rel_ctx) p !)).
+ simpl.
  refine (fun p γ γε => _).
  refine (@ext_rel_ext _ _ _ _ (γε p !) p !).
Defined.

Definition Prd {Γ : Ctx} (A : Typ Γ) (B : Typ (Ext Γ A)) : Typ Γ.
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => _).
  refine (forall
    (x : forall q (α : q ≤ p), A q (α · γ) (α · γε))
    (xε : forall q (α : q ≤ p), @typ_rel Γ A _ (α · γ) (α · γε) (α · x)), _).
  unshelve refine (B.(typ_typ _) p _ _).
  - refine (fun q α => Build_Ext_typ _ _ _ (fun r β => γ r (β ∘ α)) (α · γε) (x q α)).
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
  - refine (fun r (β : r ≤ q) => Build_Ext_typ _ _ _ (fun s ζ => γ s (ζ ∘ β ∘ α)) ((β ∘ α) · γε) (x r β)).
  - simpl; unshelve econstructor; simpl.
    { intros r β; reflexivity. }
    { refine (_ · xε). }
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
