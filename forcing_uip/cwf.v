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

Arguments eqn_rect {_ _} _ _ {_}.

Definition rew {A} (P : A -> SProp) {x y : A} (e : eqn A x y) (p : P x) : P y :=
  match e in eqn _ _ z return P z with refl _ _ => p end.

Definition transp {A} (P : A -> Type) {x y : A} (e : eqn A x y) (p : P x) : P y.
Proof.
refine (match e in eqn _ _ z return P z with refl _ _ => p end).
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
  ctx_mon : forall p q (α : q ≤ p) (γ : forall q (α : q ≤ p), ctx_typ q),
    ctx_rel p γ -> ctx_rel q (α · γ)
}.

Coercion ctx_typ : Ctx >-> Funclass.
Arguments ctx_rel _ {_}.
Arguments ctx_mon _ {_} {_} _ {_}.

Notation Θ := ctx_mon.

Record Sub (Γ Δ : Ctx) := {
  sub_fun : forall p (γ : forall q (α : q ≤ p), Γ q) (γε : ctx_rel Γ γ), Δ p;
  sub_rel : forall p (γ : forall q (α : q ≤ p), Γ q) (γε : ctx_rel Γ γ),
    ctx_rel Δ (fun q α => sub_fun q (α · γ) (Θ Γ α γε));
}.

Coercion sub_fun : Sub >-> Funclass.

Arguments sub_fun {_ _}.
Arguments sub_rel {_ _}.

Record Typ (Γ : Ctx) := {
  typ_typ : forall p (γ : forall q (α : q ≤ p), ctx_typ Γ q)
    (γε : ctx_rel Γ γ), Type;
  typ_rel : forall p γ γε (x : forall q (α : q ≤ p), typ_typ q (α · γ) (Θ Γ α γε)), SProp;
  typ_mon : forall p q (α : q ≤ p) γ γε x,
    typ_rel p γ γε x -> typ_rel q (α · γ) (Θ Γ α γε) (α · x);
}.

Coercion typ_typ : Typ >-> Funclass.
Arguments typ_rel {_} _ {_ _ _}.
Arguments typ_mon {_} _ {_ _} _ {_}.

Definition Typ_subs {Γ Δ : Ctx} (σ : Sub Δ Γ) (A : Typ Γ) : Typ Δ.
Proof.
unshelve econstructor.
+ unshelve refine (fun p δ δε => A p (fun q α => σ q (α · δ) (Θ Δ α δε)) _).
  unshelve refine (σ.(sub_rel) p δ δε).
+ unshelve refine (fun p δ δε x => @typ_rel _ A _ _ (σ.(sub_rel) p δ δε) x).
+ simpl.
  refine (fun p q α γ γε x xε => A.(typ_mon) _ _ _ xε).
Defined.

Record Trm (Γ : Ctx) (A : Typ Γ) := {
  trm_elt : forall p (γ : forall q (α : q ≤ p), ctx_typ Γ q) (γε : ctx_rel Γ γ), A p γ γε;
  trm_rel : forall p (γ : forall q (α : q ≤ p), ctx_typ Γ q) (γε : ctx_rel Γ γ),
    @typ_rel Γ A p γ γε (fun q (α : q ≤ p) => trm_elt q (α · γ) (Θ Γ α γε))
}.

Arguments trm_elt {_ _}.
Arguments trm_rel {_ _}.

Definition Trm_subs {Γ Δ : Ctx} (σ : Sub Δ Γ) {A : Typ Γ}
  (t : Trm Γ A) : Trm Δ (Typ_subs σ A).
Proof.
unshelve econstructor.
+ simpl; refine (fun p γ γε => _).
  refine (t.(trm_elt) _ _ (sub_rel σ p γ γε)).
+ simpl; refine (fun p γ γε => _).
  refine (t.(trm_rel) _ _ (sub_rel σ p γ γε)).
Defined.

Definition Nil : Ctx.
Proof.
unshelve econstructor.
+ refine (fun _ => unit).
+ refine (fun _ _ => True).
+ constructor.
Defined.

Record Ext_typ (Γ : Ctx) (A : Typ Γ) (p : ℙ) := {
  ext_typ_ctx : forall q (α : q ≤ p), Γ q;
  ext_typ_rel : ctx_rel Γ ext_typ_ctx;
  ext_typ_ext : A p ext_typ_ctx ext_typ_rel;
}.

Arguments ext_typ_ctx {_ _ _}.
Arguments ext_typ_rel {_ _ _}.
Arguments ext_typ_ext {_ _ _}.

Record Ext_rel (Γ : Ctx) (A : Typ Γ) (p : ℙ)
  (γ : forall q : ℙ, q ≤ p -> Ext_typ Γ A q) : SProp := {

  ext_rel_ctx :
    forall q (α : q ≤ p),
      eqn _ (γ q α).(ext_typ_ctx) (fun r (β : r ≤ q) => (γ r (β ∘ α)).(ext_typ_ctx) r !);
  ext_rel_ext :
    @typ_rel _ A p
      (fun q α => (γ q α).(ext_typ_ctx) q !)
      (rew (ctx_rel Γ) (ext_rel_ctx _ _) (γ p !).(ext_typ_rel))
      (fun q α =>
     eqn_rect
       (fun δ e => A q δ (rew (ctx_rel Γ) e (ext_typ_rel (γ q α)))) (γ q α).(ext_typ_ext)
        (ext_rel_ctx q α))
}.

Arguments ext_rel_ctx {_ _ _ _}.
Arguments ext_rel_ext {_ _ _ _}.

Definition Ext (Γ : Ctx) (A : Typ Γ) : Ctx.
Proof.
unshelve econstructor.
+ refine (Ext_typ Γ A).
+ refine (Ext_rel Γ A).
+ refine (fun p q α γ γε => _).
  unshelve econstructor.
  - refine (fun r β => γε.(ext_rel_ctx) r (β ∘ α)).
  - simpl.
    pose (x :=
      fun (r : ℙ) (β' : r ≤ p) =>
         eqn_rect
           (fun (c : forall q : ℙ, q ≤ r -> Γ q)
              (e : eqn (forall q : ℙ, q ≤ r -> Γ q) (ext_typ_ctx (γ r β')) c)
            => A r c (rew (ctx_rel Γ) e (ext_typ_rel (γ r β'))))
           (ext_typ_ext (γ r β')) (ext_rel_ctx γε r β')
    ).
    match goal with
    [ |- typ_rel A ?y ] => change y with (α · x)
    end.
    refine (@typ_mon _ A _ _ α (fun r β => (γ r β).(ext_typ_ctx) r !) _ x γε.(ext_rel_ext)).
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
  simpl. refine (t.(trm_rel) _ _ _).
Defined.

Definition Wkn (Γ : Ctx) (A : Typ Γ) : Sub (Ext Γ A) Γ.
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => (γ p !).(ext_typ_ctx) p !).
+ simpl.
  intros p γ γε.
  refine (rew (ctx_rel Γ) (γε.(ext_rel_ctx) p !) _).
  refine ((γ p !).(ext_typ_rel)).
Defined.

Definition Var {Γ : Ctx} {A : Typ Γ} : Trm (Ext Γ A) (Typ_subs (Wkn Γ A) A).
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => _).
  refine (eqn_rect (fun z e => A p z (rew (ctx_rel Γ) e (ext_typ_rel (γ p !)))) _ (γε.(ext_rel_ctx) p !)).
  refine (γ p !).(ext_typ_ext).
+ simpl.
  refine (fun p γ γε => _).
  refine (@ext_rel_ext _ _ _ _ γε).
Defined.

Definition Prd {Γ : Ctx} (A : Typ Γ) (B : Typ (Ext Γ A)) : Typ Γ.
Proof.
unshelve econstructor; simpl.
+ refine (fun p γ γε => _).
  refine (forall (x : forall q (α : q ≤ p), A q _ (Θ Γ α γε)) (xε : A.(typ_rel) x), _).
  unshelve refine (B.(typ_typ _) p _ _).
  - refine (fun q α => Build_Ext_typ _ _ _ (fun r β => γ r (β ∘ α)) (Θ Γ α γε) (x q α)).
  - simpl; unshelve econstructor; simpl.
    { intros q α; reflexivity. }
    { refine xε. }
+ simpl.
  refine (fun p γ γε f => _).
  unshelve refine (
    forall
      q (α : q ≤ p)
      (x : forall r (β : r ≤ q), A r _ (Θ Γ (β ∘ α) γε))
      (xε : @typ_rel _ A q (α · γ) (Θ Γ α γε) x),
      @typ_rel _ B q _ _ _
  ).
  - refine (fun r (β : r ≤ q) => Build_Ext_typ _ _ _ (fun s ζ => γ s (ζ ∘ β ∘ α)) (Θ Γ (β ∘ α) γε) (x r β)).
  - simpl; unshelve econstructor; simpl.
    { intros r β; reflexivity. }
    { refine xε. }
  - simpl.
    refine (fun r β => f r (β ∘ α) (β · x) (A.(typ_mon) β _ x _)).
+ simpl.
  refine (fun p q α γ γε f fε r β x xε => _).
  refine (fε _ _ x xε).
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

Definition App {Γ : Ctx} (A : Typ Γ) {B : Typ (Ext Γ A)}
  (t : Trm Γ (Prd A B)) (u : Trm Γ A) : Trm Γ (Typ_subs (Cns _ _ u) B).
Proof.
unshelve econstructor.
+ refine (fun p γ γε => _); simpl.
  unshelve refine (t.(trm_elt) p _ _ _ _).
+ simpl. refine (fun p γ γε => _).
  unshelve refine (t.(trm_rel) p _ _ _ _ _ _).
Defined.
