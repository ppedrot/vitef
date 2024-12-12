Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Set Primitive Projections.

Record sig (A : Type) (B : A -> Type) := pair {
  fst : A;
  snd : B fst;
}.

Arguments pair {_ _}.
Arguments fst {_ _}.
Arguments snd {_ _}.

Axiom ℙ : Set.
Axiom le0 : ℙ -> ℙ -> Set.

Definition le (p q : ℙ) := forall r, le0 q r -> le0 p r.

Notation "p ≤ q" := (le p q) (at level 70).
Notation "α ∘ β" := (fun (r : ℙ) (γ : le0 _ r) => α r (β r γ)) (at level 50).
Notation "!" := (fun (r : ℙ) (γ : le0 _ r) => γ).
Notation "α · t" := (fun (q : ℙ) (β : q ≤ _) => t q (β ∘ α)) (at level 50).

Record Ctx := {
  ctx_typ : forall (p : ℙ), Type;
}.

Coercion ctx_typ : Ctx >-> Funclass.

Record Sub (Γ Δ : Ctx) := {
  sub_fun : forall p (γ : forall q (α : q ≤ p), Γ q), Δ p;
}.

Coercion sub_fun : Sub >-> Funclass.

Record Typ (Γ : Ctx) := {
  typ_typ : forall p (γ : forall q (α : q ≤ p), Γ q), Type;
}.

Coercion typ_typ : Typ >-> Funclass.

Record Trm (Γ : Ctx) (A : Typ Γ) := {
  trm_elt : forall p (γ : forall q (α : q ≤ p), Γ q), A p γ;
}.

Arguments trm_elt {_ _}.

Definition typ_sub {Γ Δ} (A : Typ Δ) (σ : Sub Γ Δ) : Typ Γ.
Proof.
unshelve econstructor.
unshelve refine (fun p δ => A p (fun q α => σ q (α · δ))).
Defined.

Definition trm_sub {Γ Δ} {A : Typ Δ} (t : Trm Δ A) (σ : Sub Γ Δ) : Trm Γ (typ_sub A σ).
Proof.
unshelve econstructor.
simpl; refine (fun p γ => _).
refine (t.(trm_elt) _ _).
Defined.

Definition idn (Γ : Ctx) : Sub Γ Γ := Build_Sub _ _ (fun p γ => γ p !).

Definition cmp {Γ Δ Ξ : Ctx} (σ : Sub Γ Δ) (τ : Sub Δ Ξ) : Sub Γ Ξ.
Proof.
unshelve econstructor.
refine (fun p γ => τ _ (fun q α => σ q (α · γ))).
Defined.

Lemma typ_sub_idn : forall Γ A, typ_sub A (idn Γ) = A.
Proof.
reflexivity.
Defined.

Lemma typ_sub_cmp : forall Γ Δ Ξ A σ τ, typ_sub A (@cmp Γ Δ Ξ σ τ) = typ_sub (typ_sub A τ) σ.
Proof.
reflexivity.
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

Definition ext (Γ : Ctx) (A : Typ Γ) : Ctx.
Proof.
unshelve econstructor.
unshelve refine (fun p => sig _ _).
+ refine (forall q (α : q ≤ p), Γ q).
+ refine (fun γ => A p γ).
Defined.

Definition wkn {Γ Δ} (A : Typ Γ) (σ : Sub Γ Δ) : Sub (ext Γ A) Δ.
Proof.
constructor.
refine (fun p γ => σ _ (fun q α => fst (γ q α) q !)).
Defined.

Definition lft {Γ Δ} (A : Typ Δ) (σ : Sub Γ Δ) : Sub (ext Γ (typ_sub A σ)) (ext Δ A).
Proof.
constructor.
unshelve refine (fun γ => pair (σ γ.(fst)) γ.(snd)).
Defined.

Definition rel0 {Γ : Ctx} {A : Typ Γ} : Trm (ext Γ A) (typ_sub A (wkn A (idn _))).
Proof.
unshelve econstructor.
+ refine (fun γ p => γ.(snd).(fst) p).
+ refine (fun γ => γ.(snd).(snd)).
Defined.

Definition cns {Γ Δ} {A : Typ Γ} (σ : Sub Δ Γ) (x : Trm Δ (typ_sub A σ)) : Sub Δ (ext Γ A).
Proof.
unshelve econstructor.
unshelve refine (fun δ => pair (σ δ) (pair (x.(trm_elt) _) (x.(trm_rel) _))).
Defined.

Definition Π {Γ : Ctx} (A : Typ Γ) (B : Typ (ext Γ A)) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ p => forall (x : forall p, A.(typ_elt) γ p) (xε : A.(typ_rel) γ x), B.(typ_elt) (pair γ (pair x xε)) p).
+ cbn.
  unshelve refine (fun γ f => forall (x : forall p, A.(typ_elt) γ p) (xε : A.(typ_rel) γ x), B.(typ_rel) _ _).
  - refine (pair γ (pair x xε)).
  - refine (fun p => f p _ _).
Defined.

Definition lam {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm (ext Γ A) B) : Trm Γ (Π A B).
Proof.
unshelve econstructor.
+ refine (fun γ p x xε => t.(trm_elt) _ _).
+ refine (fun γ x xε => t.(trm_rel) _).
Defined.

Definition app {Γ : Ctx} {A : Typ Γ} {B : Typ (ext Γ A)} (t : Trm Γ (Π A B)) (u : Trm Γ A) :
  Trm Γ (typ_sub B (cns (idn Γ) u)).
Proof.
unshelve econstructor.
+ refine (fun γ p => t.(trm_elt) _ _ _ _).
+ refine (fun γ => t.(trm_rel) _ _ _).
Defined.

Definition Arr {Γ : Ctx} (A B : Typ Γ) := Π A (typ_sub B (wkn _ (idn _))).

Definition Squash {Γ : Ctx} (A : Typ Γ) : Typ Γ.
Proof.
unshelve econstructor.
+ refine (fun γ p => A.(typ_elt) γ p).
+ refine (fun γ _ => True).
Defined.

Lemma choice {Γ} {A : Typ Γ} {B : Typ (ext Γ A)} : Trm Γ (Arr (Π A (Squash B)) (Squash (Π A B))).
Proof.
unshelve econstructor; cbn.
+ refine (fun γ p f fε x xε => _).
  apply f.
+ constructor.
Defined.
*)
